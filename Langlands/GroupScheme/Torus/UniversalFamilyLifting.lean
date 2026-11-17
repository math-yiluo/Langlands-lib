import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction

/-! # Pointed etale torus lifting from a supplied universal family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

@[reassoc] private theorem map_fst {B A : Scheme.{u}} (q : A ⟶ B)
    {H L : GroupScheme B} (f : H ⟶ L) :
    ((baseChange q).map f).hom.hom.left ≫ pullback.fst L.X.hom q =
      pullback.fst H.X.hom q ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Successive evaluation of a subgroup family agrees with direct evaluation,
including the actual source and target pullback comparisons. -/
theorem familyHom_comparison {M T T' : Over S} {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj G) (a : T ⟶ M) (b : T' ⟶ T)
    (x : T' ⟶ M) (hx : b ≫ a = x) :
    (baseChange b.left).map (familyHom j a) ≫
        (Descent.pullbackComparison T.hom b.left T'.hom (Over.w b) G).hom =
      (Descent.pullbackComparison a.left b.left x.left
        (congrArg (fun f : T' ⟶ M => f.left) hx) K).hom ≫ familyHom j x := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      Descent.pullbackComparison_hom_fst, map_fst_assoc,
      familyHom_original,
      Descent.pullbackComparison_hom_fst_assoc]
  · exact (Over.w ((baseChange b.left).map (familyHom j a) ≫
      (Descent.pullbackComparison T.hom b.left T'.hom (Over.w b) G).hom).hom.hom).trans
      (Over.w ((Descent.pullbackComparison a.left b.left x.left
        (congrArg (fun f : T' ⟶ M => f.left) hx) K).hom ≫ familyHom j x).hom.hom).symm

private theorem represents_range_of_closed {B : Scheme.{u}} {H L : GroupScheme B}
    (f : H ⟶ L) (hf : IsClosedSubgroup f) :
    (SubgroupFunctor.range f).IsRepresentedBy f := by
  let : IsClosedImmersion f.hom.hom.left := hf
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- Actual lift data for a closed residue-fibre torus. The fibre isomorphism
recovers the specified original inclusion with explicit pullback comparisons. -/
structure PointedTorusLiftData (G : GroupScheme S) (s : S)
    (T₀ : GroupScheme (Spec (S.residueField s)))
    (i₀ : T₀ ⟶ (baseChange (S.fromSpecResidueField s)).obj G) where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ S
  etale : Etale projection
  point : Spec (S.residueField s) ⟶ neighbourhood
  point_over : point ≫ projection = S.fromSpecResidueField s
  torus : GroupScheme neighbourhood
  isTorus : RelativeTorus.IsTorus torus
  inclusion : torus ⟶ (baseChange projection).obj G
  closed : IsClosedSubgroup inclusion
  fibreIso : (baseChange point).obj torus ≅ T₀
  recovers : (baseChange point).map inclusion ≫
      (Descent.pullbackComparison projection point (S.fromSpecResidueField s)
        point_over G).hom = fibreIso.hom ≫ i₀

/-- A supplied smooth universal closed torus-subgroup family lifts every closed
relative torus in a residue fibre to a pointed etale neighbourhood. -/
theorem nonempty_pointedTorusLiftData {M : Over S} {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (huni : IsUniversal j) [Smooth M.hom]
    (s : S) (T₀ : GroupScheme (Spec (S.residueField s)))
    (hT₀ : RelativeTorus.IsTorus T₀)
    (i₀ : T₀ ⟶ (baseChange (S.fromSpecResidueField s)).obj G)
    (hi₀ : IsClosedSubgroup i₀) : Nonempty (PointedTorusLiftData G s T₀ i₀) := by
  let c := S.fromSpecResidueField s
  obtain ⟨x, hx, -⟩ := huni (Over.mk c) (SubgroupFunctor.range i₀)
    (isAdmissible_range i₀ hi₀ hT₀)
  obtain ⟨U, p, b, a, hp, hb, ha, hba⟩ :=
    Langlands.AlgebraicGeometry.exists_pointed_etale_section M.hom s x.left (Over.w x)
  let uM : Over.mk p ⟶ M := Over.homMk a ha
  let bU : Over.mk c ⟶ Over.mk p := Over.homMk b hb
  have hbM : bU ≫ uM = x := by
    apply Over.OverMorphism.ext
    exact hba
  let i := familyHom j uM
  have hix : IsClosedSubgroup (familyHom j x) := isClosedSubgroup_familyHom j hj x
  have hrep : (SubgroupFunctor.range i₀).IsRepresentedBy (familyHom j x) := by
    rw [← hx]
    exact represents_range_of_closed (familyHom j x) hix
  have hrep₀ : (SubgroupFunctor.range i₀).IsRepresentedBy i₀ :=
    represents_range_of_closed i₀ hi₀
  let e₀ := hrep.isoOfIsRepresentedBy hrep₀
  let e := Descent.pullbackComparison a b x.left hba K ≪≫ e₀
  refine ⟨⟨U, p, hp, b, hb, (baseChange a).obj K, hK.baseChange a,
    i, isClosedSubgroup_familyHom j hj uM, e, ?_⟩⟩
  change (baseChange bU.left).map (familyHom j uM) ≫
    (Descent.pullbackComparison (Over.mk p).hom bU.left (Over.mk c).hom
      (Over.w bU) G).hom = e.hom ≫ i₀
  rw [familyHom_comparison j uM bU x hbM]
  dsimp only [e, Iso.trans_hom]
  rw [Category.assoc, SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp]
  rfl

/-- Choose actual pointed etale lift data from a supplied smooth universal
closed torus-subgroup family. -/
def pointedTorusLift {M : Over S} {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (huni : IsUniversal j) [Smooth M.hom]
    (s : S) (T₀ : GroupScheme (Spec (S.residueField s)))
    (hT₀ : RelativeTorus.IsTorus T₀)
    (i₀ : T₀ ⟶ (baseChange (S.fromSpecResidueField s)).obj G)
    (hi₀ : IsClosedSubgroup i₀) : PointedTorusLiftData G s T₀ i₀ :=
  Classical.choice (nonempty_pointedTorusLiftData j hj hK huni s T₀ hT₀ i₀ hi₀)

end Langlands.GroupScheme.TorusSubgroupModuli
