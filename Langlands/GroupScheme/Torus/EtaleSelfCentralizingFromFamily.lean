import Langlands.GroupScheme.Torus.UniversalFamilyLifting
import Langlands.GroupScheme.Torus.SeparatedCentralizerModel
import Langlands.GroupScheme.Torus.SuppliedCentralizerSpreading
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Rational.TorusCentralizerConjugacy

/-! # Etale self-centralizing torus neighbourhoods from a universal family -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- An actual etale neighbourhood of a base point carrying a closed relative
maximal torus which represents its whole centralizer on every test scheme. -/
structure EtaleSelfCentralizingTorusNeighbourhood {S : Scheme.{u}}
    (G : GroupScheme S) (s : S) where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ S
  etale : Etale projection
  point : neighbourhood
  point_over : projection point = s
  torus : CommGroupScheme neighbourhood
  isTorus : RelativeTorus.IsTorus torus.toGrp
  inclusion : torus.toGrp ⟶ (baseChange projection).obj G
  closed : IsClosedSubgroup inclusion
  fibrewiseMaximal : IsFibrewiseMaximalTorus inclusion
  selfCentralizing : (torusCentralizer inclusion).IsRepresentedBy inclusion

namespace TorusSubgroupModuli

private theorem represents_range_of_closed {B : Scheme.{u}} {H L : GroupScheme B}
    (f : H ⟶ L) (hf : IsClosedSubgroup f) :
    (SubgroupFunctor.range f).IsRepresentedBy f := by
  let : IsClosedImmersion f.hom.hom.left := hf
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- From a supplied smooth universal torus family, every base point admits an
actual etale neighbourhood carrying a self-centralizing relative maximal torus.
Only local finite type, separatedness and connected reductive residue fibres
are required of the ambient group. -/
theorem nonempty_etaleSelfCentralizingTorusNeighbourhood
    {S : Scheme.{u}} {G : GroupScheme S}
    [LocallyOfFiniteType G.X.hom] [IsSeparated G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    {M : Over S} {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (huni : IsUniversal j) [Smooth M.hom]
    (s : S) : Nonempty (EtaleSelfCentralizingTorusNeighbourhood G s) := by
  let Gs := RelativeIdentityComponent.residueFiber G s
  let : Smooth Gs.X.hom := (hG s).smooth
  let : IsAffineHom Gs.X.hom := (hG s).isAffineHom
  obtain ⟨T₀, i₀, hm₀⟩ := TorusExistence.exists_isMaximalTorus Gs
  let L := pointedTorusLift j hj hK huni s T₀.toGrp hm₀.1.isRelativeTorus i₀ hm₀.2.1
  let T := L.isTorus.commGroupScheme
  let H := (baseChange L.projection).obj G
  let : LocallyOfFiniteType H.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom L.projection))
  let : IsSeparated H.X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd G.X.hom L.projection))
  have hH : HasConnectedReductiveResidueFibers H :=
    connectedReductive_residueFibers_baseChange G hG L.projection
  have hmPoint : IsMaximalTorus
      (T := (CommGroupScheme.baseChange L.point).obj T)
      ((baseChange L.point).map L.inclusion) := by
    let e := Descent.pullbackComparison L.projection L.point
      (S.fromSpecResidueField s) L.point_over G
    apply (IsMaximalTorus.comp_iso_iff _ e).mp
    rw [show (baseChange L.point).map L.inclusion ≫ e.hom =
      L.fibreIso.hom ≫ i₀ from L.recovers]
    exact IsMaximalTorus.iso_comp
      (T := T₀) (T' := (CommGroupScheme.baseChange L.point).obj T) L.fibreIso hm₀
  have hmResidue := isMaximalTorus_residueFibre_of_fieldPoint
    (T := T) L.closed L.point hmPoint
  let C := separatedRelativeTorusCentralizerModel (T := T) L.inclusion L.isTorus
  let O := selfCentralizingTorusOpen hH (T := T) L.inclusion L.isTorus L.closed
    C.hom C.represents C.closed (L.point (IsLocalRing.closedPoint (S.residueField s))) hmResidue
  let V := O.openSet
  let q := V.ι ≫ L.projection
  let TV := (CommGroupScheme.baseChange V.ι).obj T
  let tV := (baseChange V.ι).map L.inclusion
  let e := (baseChangeCompIso L.projection V.ι G).symm
  let i : TV.toGrp ⟶ (baseChange q).obj G := tV ≫ e.hom
  let : Etale L.projection := L.etale
  have hq : Etale q := inferInstance
  have htV : IsClosedSubgroup tV := L.closed.baseChange V.ι
  have hrep : (torusCentralizer (T := TV) tV).IsRepresentedBy tV := by
    rw [O.selfCentralizing]
    exact represents_range_of_closed tV htV
  have hrep' : (torusCentralizer (T := TV) i).IsRepresentedBy i :=
    hrep.torusCentralizer_of_iso_square (Iso.refl _) e (by simp [i])
  refine ⟨⟨(V : Scheme), q, hq,
    ⟨L.point (IsLocalRing.closedPoint (S.residueField s)), O.mem⟩,
    ?_, TV, L.isTorus.baseChange V.ι, i, htV.comp_iso e,
    O.fibrewiseMaximal.comp_iso e, hrep'⟩⟩
  have he := congrArg
    (fun f : Spec (S.residueField s) ⟶ S => f (IsLocalRing.closedPoint (S.residueField s)))
    L.point_over
  exact he.trans (Scheme.fromSpecResidueField_apply s _)

/-- Choose an actual etale self-centralizing maximal-torus neighbourhood from
supplied smooth universal torus-family data. -/
def etaleSelfCentralizingTorusNeighbourhood
    {S : Scheme.{u}} {G : GroupScheme S}
    [LocallyOfFiniteType G.X.hom] [IsSeparated G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    {M : Over S} {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (huni : IsUniversal j) [Smooth M.hom]
    (s : S) : EtaleSelfCentralizingTorusNeighbourhood G s :=
  Classical.choice (nonempty_etaleSelfCentralizingTorusNeighbourhood hG j hj hK huni s)

end TorusSubgroupModuli
end Langlands.GroupScheme
