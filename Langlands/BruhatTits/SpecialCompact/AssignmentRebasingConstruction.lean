import Langlands.Geometry.Building.FullValidity.InnerBuildingComparison
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.BruhatTits.SpecialCompact.ValidTorusRebasingStatement

/-! # Assignment rebasing from a supplied full-datum transport operation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- Construct a fully valid rebased assignment from a supplied general
full-datum transport law. This conditional construction isolates the remaining
local transport input; it is not an unconditional proof of torus rebasing. -/
def rebaseAssignmentFromDatumTransport
    (transport : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G H : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
      (D : KPBuildingDatum G), D.SatisfiesGroupAxioms →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ H)
        (f : G ≅ H) (σ : D.base.S ≅ S),
        D.base.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ i →
        ∃ E : KPBuildingDatum H, E.SatisfiesGroupAxioms ∧
          E.base.S = S ∧ HEq E.base.i i ∧
          ∃ Φ : D.base.ReducedBuilding ≃ E.base.ReducedBuilding,
            ValuationBuildingData.IsEquivariantBuildingIso
              D.base.toValuationBuildingData E.base.toValuationBuildingData
              (rationalPoints.map f.hom) Φ ∧
            ValuationBuildingData.IsBuildingIso
              E.base.toValuationBuildingData D.base.toValuationBuildingData Φ.symm)
    (B : KPBuildingAssignment.{u}) (hB : B.IsValid)
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    {B' : KPBuildingAssignment.{u} // B'.IsValid ∧
      (B'.datum F G hG).base.S = S ∧ HEq (B'.datum F G hG).base.i i} := by
  classical
  apply Classical.choice
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let D : KPBuildingDatum G := B.datum F G hG
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy F G hG).1
    D.base.S S D.base.i i D.base.isMaximalSplitTorus hi
  let σ : D.base.S ≅ S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  obtain ⟨E, hE, hS, hiE, Φ, hΦ, hinv⟩ := transport F G G D
    (hB F G hG).groupAxioms S i (G.innerIso g) σ he
  let p : KPBuildingAssignment.DatumIndex.{u} :=
    ⟨F, ‹Field F›, ‹ValuativeRel F›, ‹TopologicalSpace F›,
      ‹IsNonarchimedeanLocalField F›, G, ‹IsAffineHom G.X.hom›, hG⟩
  let comparison : KPBuildingDatum.BuildingEquivalence (B.datumAt p) E :=
    KPBuildingDatum.BuildingEquivalence.ofInner D E g Φ hΦ hinv
  refine ⟨⟨B.replaceDatum p E, B.replaceDatum_isValid hB p E hE comparison, ?_⟩⟩
  change ((B.replaceDatum p E).datumAt p).base.S = S ∧
    HEq ((B.replaceDatum p E).datumAt p).base.i i
  rw [B.datumAt_replaceDatum p E]
  exact ⟨hS, hiE⟩

end Langlands.BruhatTits.SpecialCompact
