import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorPointBaseChange

/-! # Original factor maps on finite-product Weil base points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

namespace WeilRestrictionFiniteProduct

variable {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)]

/-- The factor's rational test, regarded over the product base, maps to
its rational test by the original spectrum projection. -/
def factorBaseTestMap (i : ι) :
    (Over.map (finiteProductSpecProjection D i)).obj (ringTest (D i) (D i)) ⟶
      ringTest (∀ i, D i) (∀ i, D i) :=
  Over.homMk (finiteProductSpecProjection D i) (by
    change _ ≫ Spec.map (𝟙 _) = Spec.map (𝟙 _) ≫ _
    simp)

variable (C : Type u) [CommRing C] [∀ i, Algebra C (D i)]

@[reassoc (attr := simp)]
theorem testMap_left_fst (T : Over (Spec (CommRingCat.of C))) (i : ι) :
    (testMap C D T i).left ≫
        pullback.fst T.hom (Spec.algebraMap C (∀ i, D i)) =
      pullback.fst T.hom (Spec.algebraMap C (D i)) := by
  simp [testMap, FiniteProductSections.inclusion, finiteProductBaseChangeTestIso,
    pullback.congrHom, Category.assoc, ringBaseChange]

/-- The base-point comparison commutes with the original factor test. -/
theorem factorBaseTestMap_baseTest (i : ι) :
    (Over.map (finiteProductSpecProjection D i)).map
        (weilRestrictionBaseTestIso C (D i)).hom ≫ testMap C D (ringTest C C) i =
      factorBaseTestMap D i ≫ (weilRestrictionBaseTestIso C (∀ i, D i)).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.map_map_left, Category.assoc]
    rw [testMap_left_fst]
    change (weilRestrictionBaseTestIso C (D i)).hom.left ≫
        pullback.fst (Spec.algebraMap C C) (Spec.algebraMap C (D i)) =
      (factorBaseTestMap D i).left ≫
        (weilRestrictionBaseTestIso C (∀ i, D i)).hom.left ≫
          pullback.fst (Spec.algebraMap C C) (Spec.algebraMap C (∀ i, D i))
    rw [weilRestrictionBaseTestIso_hom_fst, weilRestrictionBaseTestIso_hom_fst]
    exact (finiteProductSpecProjection_comp D C i).symm
  · change (weilRestrictionBaseTestIso C (D i)).hom.left ≫
        (testMap C D (ringTest C C) i).left ≫
          pullback.snd (Spec.algebraMap C C) (Spec.algebraMap C (∀ i, D i)) =
      (factorBaseTestMap D i).left ≫
        (weilRestrictionBaseTestIso C (∀ i, D i)).hom.left ≫
          pullback.snd (Spec.algebraMap C C) (Spec.algebraMap C (∀ i, D i))
    rw [show (testMap C D (ringTest C C) i).left ≫
        pullback.snd (Spec.algebraMap C C) (Spec.algebraMap C (∀ i, D i)) =
      pullback.snd (Spec.algebraMap C C) (Spec.algebraMap C (D i)) ≫
        finiteProductSpecProjection D i from Over.w (testMap C D (ringTest C C) i)]
    rw [← Category.assoc]
    rw [show (weilRestrictionBaseTestIso C (D i)).hom.left ≫
        pullback.snd (Spec.algebraMap C C) (Spec.algebraMap C (D i)) =
      Spec.algebraMap (D i) (D i) from Over.w (weilRestrictionBaseTestIso C (D i)).hom]
    rw [show (weilRestrictionBaseTestIso C (∀ i, D i)).hom.left ≫
        pullback.snd (Spec.algebraMap C C) (Spec.algebraMap C (∀ i, D i)) =
      Spec.algebraMap (∀ i, D i) (∀ i, D i) from
        Over.w (weilRestrictionBaseTestIso C (∀ i, D i)).hom]
    change Spec.map (𝟙 _) ≫ _ = _ ≫ Spec.map (𝟙 _)
    simp [factorBaseTestMap]

variable [Finite ι]
  (Y : AlgebraicSpace (Spec (CommRingCat.of (∀ i, D i))))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction C (∀ i, D i)).obj Y.toSheaf))
  (hf : ∀ i, IsAlgebraicSpace _
    ((ringWeilRestriction C (D i)).obj (factorSpace D Y i).toSheaf))

/-- The factor projection followed by its local Weil point equivalence is
restriction of the full Weil base point along the original spectrum map. -/
theorem basePointsEquiv_factor
    (z : RingPoints C (ringWeilRestrictionSpace C (∀ i, D i) Y h) C) (i : ι) :
    ringWeilRestrictionBasePointsEquiv C (D i) (factorSpace D Y i) (hf i)
        (RingPoints.map (spaceProjection C D Y h hf i) z) =
      Y.pullback (factorBaseTestMap D i)
        (ringWeilRestrictionBasePointsEquiv C (∀ i, D i) Y h z) := by
  rw [ringWeilRestrictionBasePointsEquiv_apply,
    ringWeilRestrictionBasePointsEquiv_apply]
  change Y.pullback ((Over.map (finiteProductSpecProjection D i)).map
      (weilRestrictionBaseTestIso C (D i)).hom)
    ((ringWeilRestrictionFiniteProductPresheafIso C D Y).hom.app (op (ringTest C C)) z i) = _
  rw [ringWeilRestrictionFiniteProductPresheafIso_hom_app]
  change Y.pullback _ (Y.pullback _ z) = Y.pullback _ (Y.pullback _ z)
  rw [← pullback_comp, ← pullback_comp, factorBaseTestMap_baseTest]

end WeilRestrictionFiniteProduct

end Langlands.AlgebraicGeometry.AlgebraicSpace
