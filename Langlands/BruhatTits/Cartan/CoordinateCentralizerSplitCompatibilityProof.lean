import Langlands.BruhatTits.Cartan.CentralizerSplitCompatibilityStatement

/-! # Full centralizer compatibility on the coordinate split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.Cartan

section Evaluation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (I : Type u) [Finite I]
  {Z : GroupScheme (Spec (CommRingCat.of F))}

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I

/-- The coordinate valuation comparison evaluates the positive restriction as
normalized field order, without an identity-comparison premise. -/
private theorem eval_coordinateTorusValuationRestriction (s : (𝕋).toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s))
    (a : characterLattice 𝕋) (t : rationalPoints (𝕋).toGrp) :
    eval 𝕋 a (torusValuationRestriction s h t).toAdd =
      localFieldOrder F
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice 𝕋).symm a) t) := by
  rw [torusValuationRestriction_eq_split, SplitTorusValuation.eval_realValuation]
  rfl

end Evaluation

/-- Full V6 for the actual represented centralizer implies split-torus
compatibility for every finite coordinate split torus. -/
theorem coordinateCentralizerSplitCompatibility :
    CoordinateCentralizerSplitCompatibilityStatement.{u} := by
  intro F _ _ _ _ I _ G _ _ i _ C φ hφ a ha t u hu
  have hmap : rationalPoints.map C.j (rationalPoints.map C.s t) =
      rationalPoints.map i t := by
    change (t ≫ C.s.hom.hom) ≫ C.j.hom.hom = t ≫ i.hom.hom
    rw [Category.assoc]
    change t ≫ (C.s ≫ C.j).hom.hom = t ≫ i.hom.hom
    rw [C.comp_eq]
  have ht : eval _ a (centralizerValuation C.s C.bijective
      (rationalPoints.map C.s t)).toAdd =
      localFieldOrder F
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice _).symm a) t) :=
    eval_coordinateTorusValuationRestriction F I C.s C.bijective a t
  have hv6 := hφ a ha (rationalPoints.map C.s t) u hu
  rw [hmap, centralizerTranslation_toAdd, map_neg, ht] at hv6
  exact hv6

end Langlands.BruhatTits.Cartan
