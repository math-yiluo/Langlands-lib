import Langlands.LinearAlgebra.RationalSpan
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Rat
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Rationalization of finite-index maps of abelian groups -/

noncomputable section

open TensorProduct

namespace Langlands.LinearAlgebra.RationalSpan

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Tensoring an injective additive map with `ℚ` preserves injectivity. -/
theorem rationalization_injective (f : M →+ N) (hf : Function.Injective f) :
    Function.Injective (f.toIntLinearMap.baseChange ℚ) := by
  let : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  simpa only [LinearMap.baseChange_eq_ltensor] using
    (Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) f.toIntLinearMap hf)

/-- If each element of the target has a positive multiple in the image, the
rationalized map is surjective. No finite generation or torsion-freeness is needed. -/
theorem rationalization_surjective_of_multiples (f : M →+ N)
    (hf : ∀ n : N, ∃ d : ℕ, 0 < d ∧ d • n ∈ f.range) :
    Function.Surjective (f.toIntLinearMap.baseChange ℚ) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul q n =>
    obtain ⟨d, hd, m, hm⟩ := hf n
    refine ⟨(q / (d : ℚ)) ⊗ₜ[ℤ] m, ?_⟩
    rw [LinearMap.baseChange_tmul]
    change (q / (d : ℚ)) ⊗ₜ[ℤ] f m = _
    rw [hm, ← TensorProduct.smul_tmul]
    congr 1
    simpa only [nsmul_eq_mul] using
      mul_div_cancel₀ q (Nat.cast_ne_zero.mpr (ne_of_gt hd) : (d : ℚ) ≠ 0)
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

/-- A finite-index image implies surjectivity after rationalization. -/
theorem rationalization_surjective_of_finiteIndex (f : M →+ N)
    (hf : f.range.FiniteIndex) :
    Function.Surjective (f.toIntLinearMap.baseChange ℚ) := by
  apply rationalization_surjective_of_multiples f
  intro n
  obtain ⟨d, hd, _, hdn⟩ :=
    f.range.exists_nsmul_mem_of_index_ne_zero hf.index_ne_zero n
  exact ⟨d, hd, hdn⟩

/-- An injective additive map with finite-index image becomes bijective over `ℚ`. -/
theorem rationalization_bijective (f : M →+ N) (hinj : Function.Injective f)
    (hindex : f.range.FiniteIndex) :
    Function.Bijective (f.toIntLinearMap.baseChange ℚ) :=
  ⟨rationalization_injective f hinj, rationalization_surjective_of_finiteIndex f hindex⟩

/-- The rational linear equivalence induced by an injective finite-index map. -/
def rationalizationEquiv (f : M →+ N) (hinj : Function.Injective f)
    (hindex : f.range.FiniteIndex) : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] N) :=
  LinearEquiv.ofBijective _ (rationalization_bijective f hinj hindex)

@[simp]
theorem rationalizationEquiv_tmul (f : M →+ N) (hinj : Function.Injective f)
    (hindex : f.range.FiniteIndex) (q : ℚ) (m : M) :
    rationalizationEquiv f hinj hindex (q ⊗ₜ[ℤ] m) = q ⊗ₜ[ℤ] f m := rfl

/-- Rationalized finite-index injections preserve the natural-number dimension. -/
theorem finrank_eq_of_injective_finiteIndex (f : M →+ N) (hinj : Function.Injective f)
    (hindex : f.range.FiniteIndex) :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = Module.finrank ℚ (ℚ ⊗[ℤ] N) :=
  (rationalizationEquiv f hinj hindex).finrank_eq

end Langlands.LinearAlgebra.RationalSpan
