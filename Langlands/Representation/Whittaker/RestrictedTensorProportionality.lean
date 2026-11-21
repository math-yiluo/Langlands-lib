import Langlands.Global.RankinSelberg.FiniteWhittakerTensor

/-! # Proportionality of functionals on an algebraic restricted tensor product -/

noncomputable section
open scoped Classical TensorProduct
set_option autoImplicit false

namespace Langlands.RestrictedTensor

universe uI uV

variable {ι : Type uI} {V : ι → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (E : Finset ι) (e : ∀ i, V i)

/-- A functional regarded as a multilinear map on a finite stage. -/
def stageFunctional (L : Space ℂ V E e →ₗ[ℂ] ℂ) (S : Index E) :
    MultilinearMap ℂ (fun i : S.1 => V i) ℂ :=
  (L.comp (of ℂ V E e S)).compMultilinearMap (PiTensorProduct.tprod ℂ)

@[simp]
theorem stageFunctional_apply (L : Space ℂ V E e →ₗ[ℂ] ℂ)
    (S : Index E) (a : ∀ i : S.1, V i) :
    stageFunctional E e L S a = L (pure E e S a) :=
  rfl

private theorem exists_pure_apply_ne_zero (L : Space ℂ V E e →ₗ[ℂ] ℂ) (hL : L ≠ 0) :
    ∃ (S : Index E) (a : ∀ i : S.1, V i), L (pure E e S a) ≠ 0 := by
  by_contra! h
  apply hL
  apply LinearMap.ext
  intro w
  change L w = 0
  induction w using Langlands.RestrictedTensor.induction with
  | hpure S a => exact h S a
  | hadd w z hw hz => rw [map_add, hw, hz, add_zero]
  | hsmul c w hw => rw [map_smul, hw, smul_zero]

/-- If two functionals have the same at-most-one-dimensional slot spaces at
every finite stage, the second is a scalar multiple of the first nonzero one. -/
theorem proportional_of_stageFunctionals
    (Λ : ∀ i, Submodule ℂ (V i →ₗ[ℂ] ℂ))
    (hline : ∀ i (f g : V i →ₗ[ℂ] ℂ), f ∈ Λ i → g ∈ Λ i → f ≠ 0 →
      ∃ c : ℂ, g = c • f)
    (L₀ L₁ : Space ℂ V E e →ₗ[ℂ] ℂ) (hL₀ : L₀ ≠ 0)
    (h₀ : ∀ (S : Index E) a (i : S.1), (stageFunctional E e L₀ S).toLinearMap a i ∈ Λ i)
    (h₁ : ∀ (S : Index E) a (i : S.1), (stageFunctional E e L₁ S).toLinearMap a i ∈ Λ i) :
    ∃ c : ℂ, L₁ = c • L₀ := by
  obtain ⟨R, a₀, ha₀⟩ := exists_pure_apply_ne_zero E e L₀ hL₀
  let x₀ := pure (K := ℂ) E e R a₀
  let c := L₁ x₀ * (L₀ x₀)⁻¹
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  change L₁ w = c * L₀ w
  induction w using Langlands.RestrictedTensor.induction with
  | hpure S a =>
    let T : Index E := ⟨R.1 ∪ S.1, R.2.trans Finset.subset_union_left⟩
    have hRT : R ≤ T := Finset.subset_union_left
    have hST : S ≤ T := Finset.subset_union_right
    let b₀ : ∀ i : T.1, V i := fun i => extend e a₀ i
    let b : ∀ i : T.1, V i := fun i => extend e a i
    have hbase : pure (K := ℂ) E e T b₀ = x₀ := pure_extend E e hRT a₀
    have htest : pure (K := ℂ) E e T b = pure E e S a := pure_extend E e hST a
    let P₀ := stageFunctional E e L₀ T
    let P₁ := stageFunctional E e L₁ T
    let f (i : T.1) : V i →ₗ[ℂ] ℂ := (L₀ x₀)⁻¹ • P₀.toLinearMap b₀ i
    have hf (i : T.1) : f i ∈ Λ i := (Λ i).smul_mem _ (h₀ T b₀ i)
    have hf₀ (i : T.1) : f i (b₀ i) = 1 := by
      simp only [f, LinearMap.smul_apply, smul_eq_mul, MultilinearMap.toLinearMap_apply,
        Function.update_eq_self, P₀, stageFunctional_apply, hbase]
      exact inv_mul_cancel₀ ha₀
    have hfn (i : T.1) : f i ≠ 0 := by
      intro hz
      exact zero_ne_one (by simpa only [hz, LinearMap.zero_apply] using hf₀ i)
    have hP₀ := Global.RankinSelbergGlobal.FiniteWhittakerTensor.multilinear_eq_product
      P₀ f b₀ hf₀ (fun i d => by
        apply hline i (f i) _ (hf i) _ (hfn i)
        convert h₀ T d i using 2) b
    have hP₁ := Global.RankinSelbergGlobal.FiniteWhittakerTensor.multilinear_eq_product
      P₁ f b₀ hf₀ (fun i d => by
        apply hline i (f i) _ (hf i) _ (hfn i)
        convert h₁ T d i using 2) b
    rw [← htest]
    change P₁ b = c * P₀ b
    rw [hP₀, hP₁]
    simp only [P₀, P₁, stageFunctional_apply, hbase, c]
    calc
      _ = ((∏ i : T.1, f i (b i)) * L₁ x₀) * ((L₀ x₀)⁻¹ * L₀ x₀) := by
        rw [inv_mul_cancel₀ (show L₀ x₀ ≠ 0 from ha₀), mul_one]
      _ = _ := by ring
  | hadd w z hw hz => rw [map_add, map_add, hw, hz, mul_add]
  | hsmul a w hw => rw [map_smul, map_smul, hw, smul_eq_mul, smul_eq_mul, mul_left_comm]

end Langlands.RestrictedTensor
