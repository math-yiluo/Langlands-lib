import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorPoints
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionEvaluation

/-! # Evaluation of the original algebraic-space Weil counit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section Evaluation

variable (A B R D : Type u) [CommRing A] [CommRing B] [CommRing R] [CommRing D]
  [Algebra A B] [Algebra A R] [Algebra B D]
  (f : R →+* D)
  (hf : f.comp (algebraMap A R) = (algebraMap B D).comp (algebraMap A B))
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction A B).obj X.toSheaf))

/-- Evaluate the actual Weil counit along the specified compatible coefficient map. -/
def spaceWeilRestrictionEvaluation
    (x : RingPoints A (ringWeilRestrictionSpace A B X h) R) : RingPoints B X D :=
  X.pullback (weilRestrictionEvaluationTest A B R D f hf) x

end Evaluation

section LowerNaturality

variable (A B R R' D : Type u)
  [CommRing A] [CommRing B] [CommRing R] [CommRing R'] [CommRing D]
  [Algebra A B] [Algebra A R] [Algebra A R'] [Algebra B D]
  (f : R →+* D) (f' : R' →+* D)
  (hf : f.comp (algebraMap A R) = (algebraMap B D).comp (algebraMap A B))
  (hf' : f'.comp (algebraMap A R') = (algebraMap B D).comp (algebraMap A B))
  (g : R →ₐ[A] R') (w : f'.comp g.toRingHom = f)

include w in
/-- Evaluation commutes with the original lower coefficient change. -/
theorem spaceWeilRestrictionEvaluation_natural_lower
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction A B).obj X.toSheaf))
    (x : RingPoints A (ringWeilRestrictionSpace A B X h) R) :
    spaceWeilRestrictionEvaluation A B R' D f' hf' X h (RingPoints.changeRing g x) =
      spaceWeilRestrictionEvaluation A B R D f hf X h x := by
  change X.pullback (weilRestrictionEvaluationTest A B R' D f' hf')
    (X.pullback ((Over.pullback (Spec.algebraMap A B)).map (ringTestMap A g)) x) =
      X.pullback (weilRestrictionEvaluationTest A B R D f hf) x
  rw [← pullback_comp,
    weilRestrictionEvaluationTest_natural_lower A B R R' D f f' hf hf' g w]
  rfl

end LowerNaturality

section UpperNaturality

variable (A B R D D' : Type u)
  [CommRing A] [CommRing B] [CommRing R] [CommRing D] [CommRing D']
  [Algebra A B] [Algebra A R] [Algebra B D] [Algebra B D']
  (f : R →+* D) (f' : R →+* D')
  (hf : f.comp (algebraMap A R) = (algebraMap B D).comp (algebraMap A B))
  (hf' : f'.comp (algebraMap A R) = (algebraMap B D').comp (algebraMap A B))
  (g : D →ₐ[B] D') (w : g.toRingHom.comp f = f')

include w in
/-- Evaluation commutes with the original upper coefficient change. -/
theorem spaceWeilRestrictionEvaluation_natural_upper
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction A B).obj X.toSheaf))
    (x : RingPoints A (ringWeilRestrictionSpace A B X h) R) :
    RingPoints.changeRing g (spaceWeilRestrictionEvaluation A B R D f hf X h x) =
      spaceWeilRestrictionEvaluation A B R D' f' hf' X h x := by
  change X.pullback _ (X.pullback _ x) = X.pullback _ x
  rw [← pullback_comp,
    weilRestrictionEvaluationTest_natural_upper A B R D D' f f' hf hf' g w]

end UpperNaturality

section CompletedTensor

variable (A B R C : Type u) [CommRing A] [CommRing B] [CommRing R] [CommRing C]
  [Algebra A B] [Algebra A R] [Algebra A C]
  {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  (e : C ⊗[A] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[A] b) i = algebraMap B (D i) b)
  (g : R →ₐ[A] C) (i : ι) (f : R →+* D i)
  (hf : f.comp (algebraMap A R) = (algebraMap B (D i)).comp (algebraMap A B))
  (w : (algebraMap C (D i)).comp g.toRingHom = f)

include w in
/-- The original local tensor component is evaluation on the original whole coefficient ring. -/
theorem completedTensorSpaceWeilRestrictionPointMap_eq_evaluation
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction A B).obj X.toSheaf))
    (x : RingPoints A (ringWeilRestrictionSpace A B X h) R) :
    completedTensorSpaceWeilRestrictionPointMap A B C D e he X h
        (RingPoints.changeRing g x) i =
      spaceWeilRestrictionEvaluation A B R (D i) f hf X h x := by
  change X.pullback (completedTensorWeilRestrictionFactorTestMap A B C D e he i)
    (X.pullback ((Over.pullback (Spec.algebraMap A B)).map (ringTestMap A g)) x) =
      X.pullback (weilRestrictionEvaluationTest A B R (D i) f hf) x
  rw [← pullback_comp,
    completedTensorWeilRestrictionFactorTestMap_eq_evaluation A B R C D e he g i f hf w]
  rfl

end CompletedTensor

section Tensor

variable (A B R D : Type u) [CommRing A] [CommRing B] [CommRing R] [CommRing D]
  [Algebra A B] [Algebra A R] [Algebra B D]
  (f : R →+* D)
  (hf : f.comp (algebraMap A R) = (algebraMap B D).comp (algebraMap A B))
  (φ : B ⊗[A] R →ₐ[B] D) (w : ∀ r : R, φ (1 ⊗ₜ[A] r) = f r)

include w in
/-- The tensor point comparison is evaluation along its original lower coefficient map. -/
theorem ringWeilRestrictionPointsEquiv_eq_evaluation
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction A B).obj X.toSheaf))
    (x : RingPoints A (ringWeilRestrictionSpace A B X h) R) :
    RingPoints.changeRing φ (ringWeilRestrictionPointsEquiv A B R X h x) =
      spaceWeilRestrictionEvaluation A B R D f hf X h x := by
  have ht : ringTestMap B φ ≫ (ringBaseChangeSpectrumIso A B R).inv =
      weilRestrictionEvaluationTest A B R D f hf := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (ringTestMap B φ).left ≫ (ringBaseChangeSpectrumIso A B R).inv.left ≫
          pullback.fst (Spec.algebraMap A R) (Spec.algebraMap A B) =
        (weilRestrictionEvaluationTest A B R D f hf).left ≫
          pullback.fst (Spec.algebraMap A R) (Spec.algebraMap A B)
      rw [ringBaseChangeSpectrumIso_inv_fst, weilRestrictionEvaluationTest_fst,
        ringTestMap_left, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext w
    · exact (Over.w (ringTestMap B φ ≫ (ringBaseChangeSpectrumIso A B R).inv)).trans
        (Over.w (weilRestrictionEvaluationTest A B R D f hf)).symm
  change X.pullback _ (X.pullback _ x) = X.pullback _ x
  rw [← pullback_comp, ht]

end Tensor

end Langlands.AlgebraicGeometry.AlgebraicSpace
