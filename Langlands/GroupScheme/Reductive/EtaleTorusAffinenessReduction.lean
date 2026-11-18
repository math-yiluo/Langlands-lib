import Langlands.GroupScheme.Torus.EtaleSelfCentralizingFromFamily
import Langlands.GroupScheme.Reductive.FiberwiseAffinenessStatement
import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Etale reduction of fibrewise affineness to self-centralizing tori -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- One actual etale neighbourhood at each base point gives an etale cover. -/
def EtaleSelfCentralizingTorusNeighbourhood.cover
    {S : Scheme.{u}} {G : GroupScheme S}
    (N : ∀ s : S, EtaleSelfCentralizingTorusNeighbourhood G s) :
    Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
  Scheme.Cover.mkOfCovers S (fun s => (N s).neighbourhood)
    (fun s => (N s).projection)
    (fun s => ⟨s, (N s).point, (N s).point_over⟩) (fun s => (N s).etale)

/-- Affineness on the actual pointed etale neighbourhoods descends to the base. -/
theorem isAffineHom_of_etaleSelfCentralizingTorusNeighbourhoods
    {S : Scheme.{u}} {G : GroupScheme S}
    (N : ∀ s : S, EtaleSelfCentralizingTorusNeighbourhood G s)
    (h : ∀ s, IsAffineHom ((baseChange (N s).projection).obj G).X.hom) :
    IsAffineHom G.X.hom := by
  exact RelativeLevi.property_of_etaleCover @IsAffineHom
    (EtaleSelfCentralizingTorusNeighbourhood.cover N) G.X.hom h

/-- A supplied smooth universal torus family reduces affineness to the case
of an actual self-centralizing maximal relative torus on each etale member. -/
theorem isAffineHom_of_universalTorusFamily_of_selfCentralizing
    {S : Scheme.{u}} {G : GroupScheme S}
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    {M : Over S} {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (huni : TorusSubgroupModuli.IsUniversal j)
    [Smooth M.hom]
    (hlocal : ∀ (U : Scheme.{u}) (q : U ⟶ S), Etale q →
      ∀ (T : CommGroupScheme U) (t : T.toGrp ⟶ (baseChange q).obj G),
        RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
        IsFibrewiseMaximalTorus t → (torusCentralizer t).IsRepresentedBy t →
        IsAffineHom ((baseChange q).obj G).X.hom) : IsAffineHom G.X.hom := by
  let N := TorusSubgroupModuli.etaleSelfCentralizingTorusNeighbourhood hG j hj hK huni
  apply isAffineHom_of_etaleSelfCentralizingTorusNeighbourhoods N
  intro s
  exact hlocal (N s).neighbourhood (N s).projection (N s).etale
    (N s).torus (N s).inclusion (N s).isTorus (N s).closed
    (N s).fibrewiseMaximal (N s).selfCentralizing

/-- The exact arbitrary-base affineness target follows from universal torus
families and affineness in the supplied self-centralizing relative-torus case.
Both unproved mathematical inputs remain explicit hypotheses. -/
theorem reductiveFiberAffineness_of_torusFamilies_of_selfCentralizing
    (hfamilies : ∀ (S : Scheme.{u}) (G : GroupScheme S)
      [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
      (∀ s : S, IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
      ∃ (M : Over S) (K : GroupScheme M.left)
        (j : K ⟶ (baseChange M.hom).obj G),
        IsClosedSubgroup j ∧ RelativeTorus.IsTorus K ∧
          TorusSubgroupModuli.IsUniversal j ∧ Smooth M.hom)
    (htorus : ∀ (S : Scheme.{u}) (G : GroupScheme S)
      [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
      HasConnectedReductiveResidueFibers G →
      ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
        RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
        IsFibrewiseMaximalTorus t → (torusCentralizer t).IsRepresentedBy t →
        IsAffineHom G.X.hom) : ReductiveFiberAffinenessStatement.{u} := by
  intro S G _ _ _ hG
  obtain ⟨M, K, j, hj, hK, huni, hM⟩ := hfamilies S G (fun s => (hG s).isAffineHom)
  let : Smooth M.hom := hM
  apply isAffineHom_of_universalTorusFamily_of_selfCentralizing hG j hj hK huni
  intro U q _ T t hT ht hmax hc
  let H := (baseChange q).obj G
  let : Smooth H.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom q))
  let : IsSeparated H.X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd G.X.hom q))
  let : QuasiCompact H.X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom q))
  exact htorus U H (connectedReductive_residueFibers_baseChange G hG q)
    T t hT ht hmax hc

end Langlands.GroupScheme
