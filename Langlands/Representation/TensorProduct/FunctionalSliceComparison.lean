import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Basic.Complex.Basic

/-! # Comparing two tensor functionals on individual slices -/

noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands

universe uI uV uA

variable {ι : Type uI} [Fintype ι] [DecidableEq ι] {V : ι → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Proportionality of the two restrictions to every fixed-context slot
propagates the scalar at a nonzero base tuple to every tuple. -/
theorem multilinear_eq_mul_of_slot_comparisons
    (L₀ L₁ : MultilinearMap ℂ V ℂ)
    (hslot : ∀ b i, L₀.toLinearMap b i ≠ 0 →
      ∃ d : ℂ, L₁.toLinearMap b i = d • L₀.toLinearMap b i)
    (c : ℂ) (a₀ : ∀ i, V i) (h₀ : L₀ a₀ ≠ 0) (hc : L₁ a₀ = c * L₀ a₀) (a : ∀ i, V i) :
    L₁ a = c * L₀ a := by
  have hsingle (b : ∀ i, V i) (i : ι) (hb : L₀ b ≠ 0)
      (hs : L₁ b = c * L₀ b) (x : V i) :
      L₁ (Function.update b i x) = c * L₀ (Function.update b i x) := by
    have hne : L₀.toLinearMap b i ≠ 0 := by
      intro he
      have he' := LinearMap.congr_fun he (b i)
      exact hb (by simpa only [MultilinearMap.toLinearMap_apply, Function.update_eq_self,
        LinearMap.zero_apply] using he')
    obtain ⟨d, hd⟩ := hslot b i hne
    have hd' : L₁ b = d * L₀ b := by
      simpa only [MultilinearMap.toLinearMap_apply, Function.update_eq_self, LinearMap.smul_apply,
        smul_eq_mul] using LinearMap.congr_fun hd (b i)
    have hdc : d = c := mul_right_cancel₀ hb (hd'.symm.trans hs)
    simpa only [MultilinearMap.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul, hdc] using
      LinearMap.congr_fun hd x
  have hfinite (S : Finset ι) :
      ∀ b a : ∀ i, V i, L₀ b ≠ 0 → L₁ b = c * L₀ b →
        (∀ i, i ∉ S → a i = b i) → L₁ a = c * L₀ a := by
    induction S using Finset.induction_on with
    | empty =>
      intro b a _ hb h
      have hab : a = b := funext fun i => h i (Finset.notMem_empty i)
      simpa only [hab] using hb
    | @insert i S hi ih =>
      intro b a hb hbase hsame
      have hupdate (x : V i) : ∀ j, j ∉ S →
          Function.update a i x j = Function.update b i x j := by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self]
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact hsame j fun h => (Finset.mem_insert.mp h).elim hji hj
      let b' := Function.update b i (a i)
      by_cases hzero : L₀ b' = 0
      · let x := b i + a i
        have hb₂ : L₀ (Function.update b i x) ≠ 0 := by
          change L₀ (Function.update b i (b i + a i)) ≠ 0
          rw [L₀.map_update_add, Function.update_eq_self]
          change L₀ b + L₀ b' ≠ 0
          simpa only [hzero, add_zero] using hb
        have h₂ := ih (Function.update b i x) (Function.update a i x) hb₂
          (hsingle b i hb hbase x) (hupdate x)
        have h₁ := ih (Function.update b i (b i)) (Function.update a i (b i))
          (by simpa only [Function.update_eq_self] using hb)
          (hsingle b i hb hbase (b i)) (hupdate (b i))
        change L₁ (Function.update a i (b i + a i)) = c * L₀ (Function.update a i (b i + a i)) at h₂
        rw [L₁.map_update_add, L₀.map_update_add, Function.update_eq_self, mul_add, ← h₁] at h₂
        exact add_left_cancel h₂
      · have h := ih b' (Function.update a i (a i)) hzero
          (hsingle b i hb hbase (a i)) (hupdate (a i))
        simpa only [Function.update_eq_self] using h
  exact hfinite Finset.univ a₀ a h₀ hc (fun i hi => (hi (Finset.mem_univ i)).elim)

variable {A : Type uA} [AddCommGroup A] [Module ℂ A]

local notation "P" => PiTensorProduct ℂ V
local notation "T" => A ⊗[ℂ] P

/-- With the finite tuple held fixed, vary the separate linear factor. -/
def tensorFunctionalLinearSlice (L : T →ₗ[ℂ] ℂ) (b : ∀ i, V i) : A →ₗ[ℂ] ℂ :=
  L.comp ((TensorProduct.mk ℂ A P).flip (PiTensorProduct.tprod ℂ b))

/-- With the separate linear factor held fixed, vary the finite tuple. -/
def tensorFunctionalMultilinearSlice (L : T →ₗ[ℂ] ℂ) (a : A) : MultilinearMap ℂ V ℂ :=
  (L.comp (TensorProduct.mk ℂ A P a)).compMultilinearMap (PiTensorProduct.tprod ℂ)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem tensorFunctionalLinearSlice_apply (L : T →ₗ[ℂ] ℂ) (b : ∀ i, V i) (a : A) :
    tensorFunctionalLinearSlice L b a = L (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem tensorFunctionalMultilinearSlice_apply (L : T →ₗ[ℂ] ℂ) (a : A) (b : ∀ i, V i) :
    tensorFunctionalMultilinearSlice L a b = L (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) :=
  rfl

/-- The fixed-context slice comparisons for a pair of tensor functionals. -/
def HaveProportionalSlices (L₀ L₁ : T →ₗ[ℂ] ℂ) : Prop :=
  (∀ b, tensorFunctionalLinearSlice L₀ b ≠ 0 →
    ∃ c : ℂ, tensorFunctionalLinearSlice L₁ b = c • tensorFunctionalLinearSlice L₀ b) ∧
  (∀ a b i, (tensorFunctionalMultilinearSlice L₀ a).toLinearMap b i ≠ 0 →
    ∃ c : ℂ, (tensorFunctionalMultilinearSlice L₁ a).toLinearMap b i =
      c • (tensorFunctionalMultilinearSlice L₀ a).toLinearMap b i)

/-- Proportionality on each fixed-context slice of the two tensor
functionals gives one scalar on the full tensor product. -/
theorem tensorFunctional_proportional_of_slice_comparisons
    (L₀ L₁ : T →ₗ[ℂ] ℂ) (hL₀ : L₀ ≠ 0)
    (hA : ∀ b, tensorFunctionalLinearSlice L₀ b ≠ 0 →
      ∃ c : ℂ, tensorFunctionalLinearSlice L₁ b = c • tensorFunctionalLinearSlice L₀ b)
    (hV : ∀ a b i, (tensorFunctionalMultilinearSlice L₀ a).toLinearMap b i ≠ 0 →
      ∃ c : ℂ, (tensorFunctionalMultilinearSlice L₁ a).toLinearMap b i =
        c • (tensorFunctionalMultilinearSlice L₀ a).toLinearMap b i) :
    ∃ c : ℂ, L₁ = c • L₀ := by
  have hbase : ∃ a₀ b₀, L₀ (a₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b₀) ≠ 0 := by
    by_contra! h
    apply hL₀
    apply LinearMap.ext
    intro z
    change L₀ z = 0
    induction z using TensorProduct.inductionOn with
    | tmul a p =>
      induction p using PiTensorProduct.induction_on with
      | smul_tprod c b => rw [TensorProduct.tmul_smul, map_smul, h, smul_zero]
      | add p q hp hq => rw [TensorProduct.tmul_add, map_add, hp, hq, add_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  obtain ⟨a₀, b₀, h₀⟩ := hbase
  have hb₀ : tensorFunctionalLinearSlice L₀ b₀ ≠ 0 :=
    fun h => h₀ (LinearMap.congr_fun h a₀)
  obtain ⟨c, hc⟩ := hA b₀ hb₀
  have hgood (a : A) (ha : L₀ (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b₀) ≠ 0) (b : ∀ i, V i) :
      L₁ (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) = c * L₀ (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) :=
    multilinear_eq_mul_of_slot_comparisons (tensorFunctionalMultilinearSlice L₀ a)
      (tensorFunctionalMultilinearSlice L₁ a) (hV a) c b₀ ha (LinearMap.congr_fun hc a) b
  have hpure (a : A) (b : ∀ i, V i) :
      L₁ (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) = c * L₀ (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) := by
    by_cases h : L₀ (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b₀) = 0
    · have ha : L₀ ((a₀ + a) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b₀) ≠ 0 := by
        simpa only [TensorProduct.add_tmul, map_add, h, add_zero] using h₀
      have hs := hgood (a₀ + a) ha b
      rw [TensorProduct.add_tmul, map_add, map_add, mul_add, ← hgood a₀ h₀ b] at hs
      exact add_left_cancel hs
    · exact hgood a h b
  refine ⟨c, LinearMap.ext fun z => ?_⟩
  change L₁ z = c * L₀ z
  induction z using TensorProduct.inductionOn with
  | tmul a p =>
    induction p using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      rw [TensorProduct.tmul_smul, map_smul, map_smul, hpure, smul_eq_mul, smul_eq_mul, mul_left_comm]
    | add p q hp hq => rw [TensorProduct.tmul_add, map_add, map_add, hp, hq, mul_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

/-- Transport the tensor comparison along a linear equivalence of the carrier. -/
theorem functional_proportional_of_tensorEquiv
    {X : Type*} [AddCommGroup X] [Module ℂ X] (e : T ≃ₗ[ℂ] X)
    (ℓ₀ ℓ₁ : X →ₗ[ℂ] ℂ) (h₀ : ℓ₀ ≠ 0)
    (h : HaveProportionalSlices (ℓ₀.comp e.toLinearMap) (ℓ₁.comp e.toLinearMap)) :
    ∃ c : ℂ, ℓ₁ = c • ℓ₀ := by
  have hne : ℓ₀.comp e.toLinearMap ≠ 0 := by
    intro hz
    apply h₀
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := e.surjective x
    exact LinearMap.congr_fun hz v
  obtain ⟨c, hc⟩ := tensorFunctional_proportional_of_slice_comparisons _ _ hne h.1 h.2
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  obtain ⟨v, rfl⟩ := e.surjective x
  exact LinearMap.congr_fun hc v

end Langlands
