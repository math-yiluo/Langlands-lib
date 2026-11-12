import Langlands.Geometry.Manifold.SmoothGroupConjugation

/-! # Tangent conjugation is a Lie algebra automorphism

The derivative at the identity of `h ↦ g * h * g⁻¹` preserves the bracket of invariant vector
fields, is the identity for `g = 1`, and is multiplicative in `g`. The proof pulls invariant
vector fields back along conjugation and uses Mathlib's naturality of the Lie bracket under
pullback. -/

noncomputable section

open scoped Manifold ContDiff
open VectorField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

theorem contMDiff_conjugation (g : G) : ContMDiff I I ∞ (fun h : G => g * h * g⁻¹) :=
  (contMDiff_const.mul contMDiff_id).mul contMDiff_const

theorem mdifferentiableAt_conjugation (g x : G) :
    MDifferentiableAt I I (fun h : G => g * h * g⁻¹) x :=
  (contMDiff_conjugation I g).mdifferentiableAt (by simp)

theorem mdifferentiableAt_inv_conjugation (g x : G) :
    MDifferentiableAt I I (fun h : G => g⁻¹ * h * g) x :=
  ((contMDiff_const.mul contMDiff_id).mul contMDiff_const :
    ContMDiff I I ∞ (fun h : G => g⁻¹ * h * g)).mdifferentiableAt (by simp)

theorem mdifferentiableAt_mul_left' (g x : G) :
    MDifferentiableAt I I (fun h : G => g * h) x :=
  (contMDiff_const.mul contMDiff_id : ContMDiff I I ∞ (fun h : G => g * h)).mdifferentiableAt
    (by simp)

/-- The derivative of conjugation at any point, after left translation from the identity. -/
theorem mfderiv_conjugation_mul_left_apply (g x : G) (v : E) :
    (mfderiv I I (fun h : G => g * h * g⁻¹) x : E →L[ℝ] E)
        ((mfderiv I I (fun h : G => x * h) 1 : E →L[ℝ] E) v) =
      (mfderiv I I (fun h : G => (g * x * g⁻¹) * h) 1 : E →L[ℝ] E)
        ((groupTangentConjugation I g : E →L[ℝ] E) v) := by
  have h1 : (fun h : G => g * h * g⁻¹) ∘ (fun h : G => x * h) =
      (fun h : G => (g * x * g⁻¹) * h) ∘ (fun h : G => g * h * g⁻¹) := by
    funext h
    simp only [Function.comp_apply]
    group
  have hA : (mfderiv I I ((fun h : G => g * h * g⁻¹) ∘ (fun h : G => x * h)) 1 : E →L[ℝ] E) =
      (mfderiv I I (fun h : G => g * h * g⁻¹) (x * 1) : E →L[ℝ] E).comp
        (mfderiv I I (fun h : G => x * h) 1 : E →L[ℝ] E) :=
    mfderiv_comp (I := I) (I' := I) (I'' := I) (1 : G)
      (mdifferentiableAt_conjugation I g (x * 1)) (mdifferentiableAt_mul_left' I x 1)
  have hB : (mfderiv I I ((fun h : G => (g * x * g⁻¹) * h) ∘ (fun h : G => g * h * g⁻¹)) 1 :
        E →L[ℝ] E) =
      (mfderiv I I (fun h : G => (g * x * g⁻¹) * h) (g * 1 * g⁻¹) : E →L[ℝ] E).comp
        (mfderiv I I (fun h : G => g * h * g⁻¹) 1 : E →L[ℝ] E) :=
    mfderiv_comp (I := I) (I' := I) (I'' := I) (1 : G)
      (mdifferentiableAt_mul_left' I (g * x * g⁻¹) (g * 1 * g⁻¹))
      (mdifferentiableAt_conjugation I g 1)
  rw [h1, hB] at hA
  rw [show g * 1 * g⁻¹ = (1 : G) by group, show x * 1 = x from mul_one x] at hA
  exact (congrArg (fun T : E →L[ℝ] E => T v) hA).symm

/-- Conjugation by `g⁻¹` is a left inverse of conjugation by `g` on derivatives. -/
theorem mfderiv_inv_conjugation_comp (g x : G) :
    (mfderiv I I (fun h : G => g⁻¹ * h * g) (g * x * g⁻¹) : E →L[ℝ] E).comp
        (mfderiv I I (fun h : G => g * h * g⁻¹) x : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
  have hc : (fun h : G => g⁻¹ * h * g) ∘ (fun h : G => g * h * g⁻¹) = id := by
    funext h
    simp only [Function.comp_apply, id]
    group
  have hA : (mfderiv I I ((fun h : G => g⁻¹ * h * g) ∘ (fun h : G => g * h * g⁻¹)) x :
        E →L[ℝ] E) =
      (mfderiv I I (fun h : G => g⁻¹ * h * g) (g * x * g⁻¹) : E →L[ℝ] E).comp
        (mfderiv I I (fun h : G => g * h * g⁻¹) x : E →L[ℝ] E) :=
    mfderiv_comp (I := I) (I' := I) (I'' := I) x
      (mdifferentiableAt_inv_conjugation I g (g * x * g⁻¹)) (mdifferentiableAt_conjugation I g x)
  rw [hc, mfderiv_id] at hA
  exact hA.symm

/-- Conjugation by `g⁻¹` is a right inverse of conjugation by `g` on derivatives. -/
theorem mfderiv_conjugation_comp_inv (g x : G) :
    (mfderiv I I (fun h : G => g * h * g⁻¹) x : E →L[ℝ] E).comp
        (mfderiv I I (fun h : G => g⁻¹ * h * g) (g * x * g⁻¹) : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E := by
  have hc : (fun h : G => g * h * g⁻¹) ∘ (fun h : G => g⁻¹ * h * g) = id := by
    funext h
    simp only [Function.comp_apply, id]
    group
  have hA : (mfderiv I I ((fun h : G => g * h * g⁻¹) ∘ (fun h : G => g⁻¹ * h * g))
        (g * x * g⁻¹) : E →L[ℝ] E) =
      (mfderiv I I (fun h : G => g * h * g⁻¹) (g⁻¹ * (g * x * g⁻¹) * g) : E →L[ℝ] E).comp
        (mfderiv I I (fun h : G => g⁻¹ * h * g) (g * x * g⁻¹) : E →L[ℝ] E) :=
    mfderiv_comp (I := I) (I' := I) (I'' := I) (g * x * g⁻¹)
      (mdifferentiableAt_conjugation I g (g⁻¹ * (g * x * g⁻¹) * g))
      (mdifferentiableAt_inv_conjugation I g (g * x * g⁻¹))
  rw [hc, mfderiv_id, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hA
  exact hA.symm

/-- The inverse of the derivative of conjugation is the derivative of inverse conjugation. -/
theorem inverse_mfderiv_conjugation (g x : G) :
    ((mfderiv I I (fun h : G => g * h * g⁻¹) x).inverse : E →L[ℝ] E) =
      (mfderiv I I (fun h : G => g⁻¹ * h * g) (g * x * g⁻¹) : E →L[ℝ] E) :=
  ContinuousLinearMap.inverse_eq (mfderiv_conjugation_comp_inv I g x)
    (mfderiv_inv_conjugation_comp I g x)

/-- Pulling back the invariant field of `Ad(g) v` along conjugation gives that of `v`. -/
theorem mpullback_conjugation_mulInvariantVectorField (g : G) (v : GroupLieAlgebra I G) :
    mpullback I I (fun h : G => g * h * g⁻¹)
        (mulInvariantVectorField (groupTangentConjugation I g v)) =
      mulInvariantVectorField v := by
  funext x
  change ((mfderiv I I (fun h : G => g * h * g⁻¹) x).inverse : E →L[ℝ] E)
      ((mfderiv I I (fun h : G => (g * x * g⁻¹) * h) 1 : E →L[ℝ] E)
        ((groupTangentConjugation I g : E →L[ℝ] E) v)) =
    (mfderiv I I (fun h : G => x * h) 1 : E →L[ℝ] E) v
  rw [inverse_mfderiv_conjugation, ← mfderiv_conjugation_mul_left_apply]
  exact congrArg (fun T : E →L[ℝ] E => T ((mfderiv I I (fun h : G => x * h) 1 : E →L[ℝ] E) v))
    (mfderiv_inv_conjugation_comp I g x)

/-- Tangent conjugation preserves the Lie bracket of invariant vector fields. -/
theorem groupTangentConjugation_lie [CompleteSpace E] (g : G) (v w : GroupLieAlgebra I G) :
    groupTangentConjugation I g ⁅v, w⁆ =
      ⁅groupTangentConjugation I g v, groupTangentConjugation I g w⁆ := by
  let : LieGroup I (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) (by simp)
  have key := mpullback_mlieBracket (I := I) (I' := I) (n := ∞)
    (f := fun h : G => g * h * g⁻¹)
    (V := mulInvariantVectorField (groupTangentConjugation I g v))
    (W := mulInvariantVectorField (groupTangentConjugation I g w)) (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField _) (mdifferentiableAt_mulInvariantVectorField _)
    (contMDiff_conjugation I g).contMDiffAt (by simp)
  rw [mpullback_conjugation_mulInvariantVectorField,
    mpullback_conjugation_mulInvariantVectorField] at key
  change ((mfderiv I I (fun h : G => g * h * g⁻¹) 1).inverse : E →L[ℝ] E)
      (mlieBracket I (mulInvariantVectorField (groupTangentConjugation I g v))
        (mulInvariantVectorField (groupTangentConjugation I g w)) (g * 1 * g⁻¹)) = ⁅v, w⁆ at key
  rw [inverse_mfderiv_conjugation, show g * 1 * g⁻¹ = (1 : G) by group] at key
  rw [← key]
  have hinv := mfderiv_conjugation_comp_inv I g 1
  rw [show g * 1 * g⁻¹ = (1 : G) by group] at hinv
  exact congrArg (fun T : E →L[ℝ] E => T (⁅groupTangentConjugation I g v,
    groupTangentConjugation I g w⁆ : GroupLieAlgebra I G)) hinv

omit [LieGroup I ∞ G] in
theorem groupTangentConjugation_one :
    (groupTangentConjugation I (1 : G) : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
  unfold groupTangentConjugation
  have h : (fun h : G => 1 * h * 1⁻¹) = id := by
    funext h
    simp
  rw [h, mfderiv_id]
  rfl

theorem groupTangentConjugation_mul (g k : G) :
    (groupTangentConjugation I (g * k) : E →L[ℝ] E) =
      (groupTangentConjugation I g : E →L[ℝ] E).comp (groupTangentConjugation I k) := by
  unfold groupTangentConjugation
  have hc : (fun h : G => g * k * h * (g * k)⁻¹) =
      (fun h : G => g * h * g⁻¹) ∘ (fun h : G => k * h * k⁻¹) := by
    funext h
    simp only [Function.comp_apply]
    group
  have hA : (mfderiv I I ((fun h : G => g * h * g⁻¹) ∘ (fun h : G => k * h * k⁻¹)) 1 :
        E →L[ℝ] E) =
      (mfderiv I I (fun h : G => g * h * g⁻¹) (k * 1 * k⁻¹) : E →L[ℝ] E).comp
        (mfderiv I I (fun h : G => k * h * k⁻¹) 1 : E →L[ℝ] E) :=
    mfderiv_comp (I := I) (I' := I) (I'' := I) (1 : G)
      (mdifferentiableAt_conjugation I g (k * 1 * k⁻¹)) (mdifferentiableAt_conjugation I k 1)
  rw [hc, hA, show k * 1 * k⁻¹ = (1 : G) by group]

theorem groupTangentConjugation_inv_apply (g : G) (v : GroupLieAlgebra I G) :
    groupTangentConjugation I g⁻¹ (groupTangentConjugation I g v) = v := by
  have h := congrArg (fun T : E →L[ℝ] E => T v) (groupTangentConjugation_mul I g⁻¹ g)
  rw [inv_mul_cancel, groupTangentConjugation_one] at h
  exact h.symm

theorem groupTangentConjugation_apply_inv (g : G) (v : GroupLieAlgebra I G) :
    groupTangentConjugation I g (groupTangentConjugation I g⁻¹ v) = v := by
  have h := congrArg (fun T : E →L[ℝ] E => T v) (groupTangentConjugation_mul I g g⁻¹)
  rw [mul_inv_cancel, groupTangentConjugation_one] at h
  exact h.symm

variable [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G]

/-- Tangent conjugation as a real Lie algebra automorphism of the identity tangent space. -/
def groupTangentConjugationLieEquiv (g : G) :
    GroupLieAlgebra I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G where
  toFun := groupTangentConjugation I g
  map_add' := map_add _
  map_smul' := map_smul _
  map_lie' := groupTangentConjugation_lie I g _ _
  invFun := groupTangentConjugation I g⁻¹
  left_inv := groupTangentConjugation_inv_apply I g
  right_inv := groupTangentConjugation_apply_inv I g

@[simp]
theorem groupTangentConjugationLieEquiv_apply (g : G) (v : GroupLieAlgebra I G) :
    groupTangentConjugationLieEquiv I g v = groupTangentConjugation I g v := rfl

end Langlands.Geometry.Manifold
