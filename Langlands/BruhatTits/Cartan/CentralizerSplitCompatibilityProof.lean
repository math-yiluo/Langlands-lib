import Langlands.BruhatTits.Cartan.CentralizerSplitCompatibilityStatement

/-! # Full centralizer compatibility on a maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.Cartan

section Evaluation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- With the identity comparison supplied, the positive torus restriction
evaluates as the normalized field order used by the apartment data. -/
private theorem eval_torusValuationRestriction_of_id (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s))
    (hS : Function.Bijective (restrictionEvaluation (𝟙 S.toGrp)))
    (a : characterLattice S) (t : rationalPoints S.toGrp) :
    eval S a (torusValuationRestriction s h t).toAdd =
      localFieldOrder F
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) t) := by
  rw [torusValuationRestriction_eq_id s h hS]
  have ht := centralizerValuation_spec (𝟙 S.toGrp) hS t
    ((rationalCharacters.equivCharacterLattice S).symm a)
  simpa [characterRestriction, characterRestrict_id, localFieldOrder] using ht

end Evaluation

/-- Full V6 for the actual represented centralizer implies split-torus
compatibility, under the explicit identity character comparison. -/
theorem centralizerSplitCompatibility :
    CentralizerSplitCompatibilityStatement.{u} := by
  intro F _ _ _ _ G _ _ S i _ C hS φ hφ a ha t u hu
  have hmap : rationalPoints.map C.j (rationalPoints.map C.s t) =
      rationalPoints.map i t := by
    change (t ≫ C.s.hom.hom) ≫ C.j.hom.hom = t ≫ i.hom.hom
    rw [Category.assoc]
    change t ≫ (C.s ≫ C.j).hom.hom = t ≫ i.hom.hom
    rw [C.comp_eq]
  have ht : eval S a (centralizerValuation C.s C.bijective
      (rationalPoints.map C.s t)).toAdd =
      localFieldOrder F
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) t) :=
    eval_torusValuationRestriction_of_id C.s C.bijective hS a t
  have hv6 := hφ a ha (rationalPoints.map C.s t) u hu
  rw [hmap, centralizerTranslation_toAdd, map_neg, ht] at hv6
  exact hv6

end Langlands.BruhatTits.Cartan
