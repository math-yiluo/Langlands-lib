import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionNaturality

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section Test

variable (A B R D : Type u) [CommRing A] [CommRing B] [CommRing R] [CommRing D]
  [Algebra A B] [Algebra A R] [Algebra B D]
  (f : R →+* D)
  (hf : f.comp (algebraMap A R) = (algebraMap B D).comp (algebraMap A B))

/-- The actual upper test spectrum over a lower coefficient map and the original upper base. -/
def weilRestrictionEvaluationTest :
    ringTest B D ⟶ ringBaseChange A B (ringTest A R) :=
  Over.homMk
    (pullback.lift (Spec.map (CommRingCat.ofHom f)) (Spec.algebraMap B D) (by
      change Spec.map (CommRingCat.ofHom f) ≫ Spec.algebraMap A R =
        Spec.algebraMap B D ≫ Spec.algebraMap A B
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hf))
    (pullback.lift_snd _ _ _)

/-- The lower coordinate of the original evaluation test is the specified coefficient map. -/
@[reassoc (attr := simp)]
theorem weilRestrictionEvaluationTest_fst :
    (weilRestrictionEvaluationTest A B R D f hf).left ≫
      pullback.fst (Spec.algebraMap A R) (Spec.algebraMap A B) =
        Spec.map (CommRingCat.ofHom f) :=
  pullback.lift_fst _ _ _

variable [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- Evaluate the original relative Weil counit at an arbitrary compatible upper test coefficient. -/
def weilRestrictionEvaluation
    (p : RingPoint A (affineChartWeilRestriction A B Y) R) : RingPoint B Y D :=
  weilRestrictionEvaluationTest A B R D f hf ≫
    affineChartWeilRestrictionComparison A B Y (ringTest A R) p

end Test

section LowerNaturality

variable (A B R R' D : Type u)
  [CommRing A] [CommRing B] [CommRing R] [CommRing R'] [CommRing D]
  [Algebra A B] [Algebra A R] [Algebra A R'] [Algebra B D]
  (f : R →+* D) (f' : R' →+* D)
  (hf : f.comp (algebraMap A R) = (algebraMap B D).comp (algebraMap A B))
  (hf' : f'.comp (algebraMap A R') = (algebraMap B D).comp (algebraMap A B))
  (h : R →ₐ[A] R') (w : f'.comp h.toRingHom = f)

include w in
/-- Evaluation tests commute with a compatible original lower coefficient change. -/
theorem weilRestrictionEvaluationTest_natural_lower :
    weilRestrictionEvaluationTest A B R' D f' hf' ≫
        (Over.pullback (Spec.algebraMap A B)).map (ringTestMap A h) =
      weilRestrictionEvaluationTest A B R D f hf := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ _ = _
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst, ringTestMap_left]
    erw [weilRestrictionEvaluationTest_fst_assoc, weilRestrictionEvaluationTest_fst]
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext w
  · exact (Over.w (weilRestrictionEvaluationTest A B R' D f' hf' ≫
        (Over.pullback (Spec.algebraMap A B)).map (ringTestMap A h))).trans
      (Over.w (weilRestrictionEvaluationTest A B R D f hf)).symm

variable [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

include w in
/-- Lower coefficient extension commutes with the actual relative Weil counit. -/
theorem weilRestrictionEvaluation_natural_lower
    (p : RingPoint A (affineChartWeilRestriction A B Y) R) :
    weilRestrictionEvaluation A B R' D f' hf' Y (p.changeRing h) =
      weilRestrictionEvaluation A B R D f hf Y p := by
  change _ ≫ affineChartWeilRestrictionComparison A B Y (ringTest A R')
    (ringTestMap A h ≫ p) = _
  rw [affineChartWeilRestrictionComparison_natural, ← Category.assoc,
    weilRestrictionEvaluationTest_natural_lower A B R R' D f f' hf hf' h w]
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
/-- Evaluation tests commute with a compatible original upper coefficient change. -/
theorem weilRestrictionEvaluationTest_natural_upper :
    ringTestMap B g ≫ weilRestrictionEvaluationTest A B R D f hf =
      weilRestrictionEvaluationTest A B R D' f' hf' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ _ = _
    erw [Category.assoc, weilRestrictionEvaluationTest_fst,
      weilRestrictionEvaluationTest_fst, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext w
  · exact (Over.w (ringTestMap B g ≫ weilRestrictionEvaluationTest A B R D f hf)).trans
      (Over.w (weilRestrictionEvaluationTest A B R D' f' hf')).symm

variable [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

include w in
/-- Upper coefficient extension commutes with the actual relative Weil counit. -/
theorem weilRestrictionEvaluation_natural_upper
    (p : RingPoint A (affineChartWeilRestriction A B Y) R) :
    (weilRestrictionEvaluation A B R D f hf Y p).changeRing g =
      weilRestrictionEvaluation A B R D' f' hf' Y p := by
  change _ ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc,
    weilRestrictionEvaluationTest_natural_upper A B R D D' f f' hf hf' g w]

end UpperNaturality

section CompletedTensor

variable (A B R C : Type u) [CommRing A] [CommRing B] [CommRing R] [CommRing C]
  [Algebra A B] [Algebra A R] [Algebra A C]
  {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  (e : C ⊗[A] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[A] b) i = algebraMap B (D i) b)
  (h : R →ₐ[A] C) (i : ι) (f : R →+* D i)
  (hf : f.comp (algebraMap A R) = (algebraMap B (D i)).comp (algebraMap A B))
  (w : (algebraMap C (D i)).comp h.toRingHom = f)

include w in
/-- Each original tensor factor test is the canonical evaluation at its original coefficient map. -/
theorem completedTensorWeilRestrictionFactorTestMap_eq_evaluation :
    completedTensorWeilRestrictionFactorTestMap A B C D e he i ≫
        (Over.pullback (Spec.algebraMap A B)).map (ringTestMap A h) =
      weilRestrictionEvaluationTest A B R (D i) f hf := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ _ = _
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst, ringTestMap_left]
    erw [completedTensorWeilRestrictionFactorTestMap_fst_assoc,
      weilRestrictionEvaluationTest_fst]
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext w
  · exact (Over.w (completedTensorWeilRestrictionFactorTestMap A B C D e he i ≫
        (Over.pullback (Spec.algebraMap A B)).map (ringTestMap A h))).trans
      (Over.w (weilRestrictionEvaluationTest A B R (D i) f hf)).symm

variable [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

include w in
/-- The original completed-tensor local counit equals evaluation on the original whole coefficient ring. -/
theorem completedTensorWeilRestrictionPointMap_eq_evaluation
    (p : RingPoint A (affineChartWeilRestriction A B Y) R) :
    completedTensorWeilRestrictionPointMap A B C D e he Y (p.changeRing h) i =
      weilRestrictionEvaluation A B R (D i) f hf Y p := by
  change _ ≫ affineChartWeilRestrictionComparison A B Y (ringTest A C)
      (ringTestMap A h ≫ p) = _ ≫ _
  rw [affineChartWeilRestrictionComparison_natural, ← Category.assoc,
    completedTensorWeilRestrictionFactorTestMap_eq_evaluation A B R C D e he h i f hf w]

end CompletedTensor

end Langlands.AlgebraicGeometry.PointTopology
