import Langlands.Global.ArchimedeanCartanTensorAction
import Langlands.Global.ArchimedeanCartanHomogeneousGenerators

/-! # Actual degree bounds and homogeneous compact covariants -/

noncomputable section
universe u
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Global.ArchimedeanGL

open Langlands.Algebra.SymmetricGrading
open Langlands.Algebra.UniversalEnveloping

variable (K : Type u) [Field K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual covariants whose tensor representatives satisfy the given degree bound. -/
def cartanSymmetricCovariantDegreeFiltration (τ : ContinuousCompactRep K n) (d : ℕ) :
    Submodule ℂ (cartanSymmetricCovariants K n τ) :=
  (cartanSymmetricTensorDegreeFiltration K n τ d).comap
    ((cartanSymmetricCovariants K n τ).restrictScalars ℂ).subtype

@[simp]
theorem mem_cartanSymmetricCovariantDegreeFiltration (τ : ContinuousCompactRep K n)
    (d : ℕ) (x : cartanSymmetricCovariants K n τ) :
    x ∈ cartanSymmetricCovariantDegreeFiltration K n τ d ↔
      x.val ∈ cartanSymmetricTensorDegreeFiltration K n τ d := Iff.rfl

theorem cartanHomogeneousSpan_le_degreeFiltration (d : ℕ) :
    homogeneousSpan ℂ (ComplexCartanComplement K n) d ≤
      cartanSymmetricDegreeFiltration K n d := by
  apply Submodule.span_le.mpr
  rintro P ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨l, hl.le, rfl⟩

theorem cartanSymmetricComponent_mem_degreeFiltration (d : ℕ)
    (P : CartanSymmetricAlgebra K n) :
    cartanSymmetricComponent K n d P ∈ cartanSymmetricDegreeFiltration K n d :=
  cartanHomogeneousSpan_le_degreeFiltration K n d
    (component_mem_homogeneousSpan ℂ (ComplexCartanComplement K n) d P)

theorem lieSymmetricComponent_mem_degreeFiltration (d : ℕ)
    (P : LieSymmetricAlgebra K n) :
    lieSymmetricComponent K n d P ∈ lieSymmetricDegreeFiltration K n d :=
  homogeneousSpan_le_symmetricDegreeFiltration ℂ (ComplexLieAlgebra K n) d
    (component_mem_homogeneousSpan ℂ (ComplexLieAlgebra K n) d P)

theorem cartanSymmetricComponent_eq_zero_of_mem_degreeFiltration {d e : ℕ}
    {P : CartanSymmetricAlgebra K n} (hP : P ∈ cartanSymmetricDegreeFiltration K n d)
    (he : d < e) : cartanSymmetricComponent K n e P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    simp only [cartanSymmetricComponent, component_prod,
      show l.length ≠ e from by omega, ↓reduceIte]
  | zero => exact map_zero _
  | add P Q hP hQ ihP ihQ => simp only [map_add, ihP, ihQ, add_zero]
  | smul z P hP ih => simp only [map_smul, ih, smul_zero]

theorem cartanSymmetricTensorComponent_mem_degreeFiltration
    (τ : ContinuousCompactRep K n) (d : ℕ) (x : CartanSymmetricCovariantModule K n τ) :
    cartanSymmetricTensorComponent K n τ d x ∈
      cartanSymmetricTensorDegreeFiltration K n τ d := by
  induction x using TensorProduct.inductionOn with
  | tmul P v =>
    exact tmul_mem_cartanSymmetricTensorDegreeFiltration K n τ
      (cartanSymmetricComponent_mem_degreeFiltration K n d P) v
  | add x y hx hy =>
    simpa only [map_add] using
      (cartanSymmetricTensorDegreeFiltration K n τ d).add_mem hx hy

theorem cartanSymmetricTensorComponent_eq_zero_of_mem_degreeFiltration
    (τ : ContinuousCompactRep K n) {d e : ℕ} {x : CartanSymmetricCovariantModule K n τ}
    (hx : x ∈ cartanSymmetricTensorDegreeFiltration K n τ d) (he : d < e) :
    cartanSymmetricTensorComponent K n τ e x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, hP, v, rfl⟩ := hx
    simp only [cartanSymmetricTensorComponent, tensorComponent_tmul,
      cartanSymmetricComponent_eq_zero_of_mem_degreeFiltration K n hP he,
      TensorProduct.zero_tmul]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, add_zero]
  | smul z x hx ih => simp only [map_smul, ih, smul_zero]

private theorem sum_range_actual_components_mono (τ : ContinuousCompactRep K n)
    (x : CartanSymmetricCovariantModule K n τ) {a b : ℕ} (hab : a ≤ b)
    (hx : ∀ e, a < e → cartanSymmetricTensorComponent K n τ e x = 0) :
    ∑ e ∈ Finset.range (b + 1), cartanSymmetricTensorComponent K n τ e x =
      ∑ e ∈ Finset.range (a + 1), cartanSymmetricTensorComponent K n τ e x := by
  apply (Finset.sum_subset (Finset.range_mono (by omega)) _).symm
  intro e he hea
  apply hx e
  simp only [Finset.mem_range] at hea
  omega

/-- The existing actual degree bound is exactly the vanishing of higher components. -/
theorem mem_cartanSymmetricTensorDegreeFiltration_iff_components
    (τ : ContinuousCompactRep K n) (d : ℕ) (x : CartanSymmetricCovariantModule K n τ) :
    x ∈ cartanSymmetricTensorDegreeFiltration K n τ d ↔
      ∀ e, d < e → cartanSymmetricTensorComponent K n τ e x = 0 := by
  constructor
  · intro hx e he
    exact cartanSymmetricTensorComponent_eq_zero_of_mem_degreeFiltration K n τ hx he
  · intro hx
    obtain ⟨D, hz, hs⟩ :=
      exists_tensorComponent_bound ℂ (ComplexCartanComplement K n) (Fin τ.dim → ℂ) x
    rw [← hs]
    apply Submodule.sum_mem
    intro e he
    by_cases hed : e ≤ d
    · exact cartanSymmetricTensorDegreeFiltration_mono K n τ hed
        (cartanSymmetricTensorComponent_mem_degreeFiltration K n τ e x)
    · rw [hx e (by omega)]
      exact Submodule.zero_mem _

/-- A bounded tensor is the sum of its canonical components up to that same bound. -/
theorem sum_cartanSymmetricTensorComponents_of_mem_degreeFiltration
    (τ : ContinuousCompactRep K n) {d : ℕ} {x : CartanSymmetricCovariantModule K n τ}
    (hx : x ∈ cartanSymmetricTensorDegreeFiltration K n τ d) :
    ∑ e ∈ Finset.range (d + 1), cartanSymmetricTensorComponent K n τ e x = x := by
  obtain ⟨D, hz, hs⟩ :=
    exists_tensorComponent_bound ℂ (ComplexCartanComplement K n) (Fin τ.dim → ℂ) x
  calc
    _ = ∑ e ∈ Finset.range (max d D + 1),
        cartanSymmetricTensorComponent K n τ e x :=
      (sum_range_actual_components_mono K n τ x (Nat.le_max_left d D)
        (fun e he => cartanSymmetricTensorComponent_eq_zero_of_mem_degreeFiltration
          K n τ hx he)).symm
    _ = ∑ e ∈ Finset.range (D + 1), cartanSymmetricTensorComponent K n τ e x :=
      sum_range_actual_components_mono K n τ x (Nat.le_max_right d D) hz
    _ = x := hs

theorem cartanSymmetricCovariantComponent_mem_degreeFiltration
    (τ : ContinuousCompactRep K n) (d : ℕ) (x : cartanSymmetricCovariants K n τ) :
    cartanSymmetricCovariantComponent K n τ d x ∈
      cartanSymmetricCovariantDegreeFiltration K n τ d :=
  cartanSymmetricTensorComponent_mem_degreeFiltration K n τ d x.val

theorem IsHomogeneousCartanCovariant.mem_degreeFiltration
    {τ : ContinuousCompactRep K n} {d : ℕ} {x : cartanSymmetricCovariants K n τ}
    (hx : IsHomogeneousCartanCovariant K n τ d x) :
    x ∈ cartanSymmetricCovariantDegreeFiltration K n τ d := by
  change x.val ∈ cartanSymmetricTensorDegreeFiltration K n τ d
  rw [← hx]
  exact cartanSymmetricTensorComponent_mem_degreeFiltration K n τ d x.val

/-- A bounded fixed covariant has a decomposition into fixed homogeneous components
with no increase of the upper bound. -/
theorem sum_cartanSymmetricCovariantComponents_of_mem_degreeFiltration
    (τ : ContinuousCompactRep K n) {d : ℕ} {x : cartanSymmetricCovariants K n τ}
    (hx : x ∈ cartanSymmetricCovariantDegreeFiltration K n τ d) :
    ∑ e ∈ Finset.range (d + 1), cartanSymmetricCovariantComponent K n τ e x = x := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, cartanSymmetricCovariantComponent_coe] using
    sum_cartanSymmetricTensorComponents_of_mem_degreeFiltration K n τ (x := x.val) hx

end Langlands.Global.ArchimedeanGL
