import Langlands.Representation.Archimedean.CompactPolynomialSections
import Langlands.Representation.FiniteVectors

/-! # Right translation orbits of vector-valued coordinate polynomials -/

noncomputable section

open scoped ContDiff

set_option autoImplicit false

universe u v w

namespace Langlands.Archimedean

variable {A : Type u} [NormedRing A]
variable {G : Type v} [Monoid G]
variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (ι : G →* Aˣ)

/-- Right multiplication by matrix units acts on vector-valued matrix functions. -/
def matrixRightTranslation : Representation ℂ G (A → V) where
  toFun k := LinearMap.funLeft ℂ V fun a => a * (ι k).val
  map_one' := LinearMap.ext fun f => funext fun a => by
    change f (a * (ι 1).val) = f a
    rw [map_one, Units.val_one, mul_one]
  map_mul' k l := LinearMap.ext fun f => funext fun a => by
    change f (a * (ι (k * l)).val) = f ((a * (ι k).val) * (ι l).val)
    rw [map_mul, Units.val_mul, mul_assoc]

@[simp]
theorem matrixRightTranslation_apply (k : G) (f : A → V) (a : A) :
    matrixRightTranslation ι k f a = f (a * (ι k).val) := rfl

variable (p : A → V)

/-- The orbit under a unit subgroup of a coordinate polynomial is finite-dimensional. -/
theorem matrixRightTranslation_isFiniteVector [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
    (hp : p ∈ vectorCoordinatePolynomials A V) :
    FiniteVectors.IsFiniteVector (matrixRightTranslation ι) p := by
  let P := Submodule.span ℂ (Set.range fun b : A => fun a : A => p (a * b))
  let : FiniteDimensional ℂ P := finiteDimensional_rightTranslateSpan_of_mem_vectorCoordinatePolynomials hp
  apply Submodule.finiteDimensional_of_le (S₂ := P)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨(ι k).val, rfl⟩

/-- Smoothness extends to the span of the matrix right translates. -/
theorem contDiff_of_mem_matrixRightTranslation_orbitSpan [NormedAlgebra ℝ A]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] (hp : ContDiff ℝ ∞ p)
    {q : A → V} (hq : q ∈ FiniteVectors.orbitSpan (matrixRightTranslation ι) p) :
    ContDiff ℝ ∞ q := by
  induction hq using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    exact hp.comp (contDiff_id.mul contDiff_const)
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact contDiff_const.smul hx

/-- Left covariance of the evaluation in a coefficient space extends to the
span of all right translates. -/
theorem matrixRightTranslation_orbitSpan_covariant
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (j : V →ₗ[ℂ] W) (t : A) (D : Module.End ℂ W)
    (h : ∀ a, j (p (t * a)) = D (j (p a)))
    {q : A → V} (hq : q ∈ FiniteVectors.orbitSpan (matrixRightTranslation ι) p) (a : A) :
    j (q (t * a)) = D (j (q a)) := by
  induction hq using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    simpa only [matrixRightTranslation_apply, mul_assoc] using h (a * (ι k).val)
  | zero => simp only [Pi.zero_apply, map_zero]
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add, hx, hy]
  | smul c x _ hx => simp only [Pi.smul_apply, map_smul, hx]

end Langlands.Archimedean
