import Langlands.Global.ArchimedeanCartanFilteredSpanning
import Langlands.Global.ArchimedeanCartanCovariants

/-! # Bounded Cartan tensor actions on genuine enveloping modules -/

noncomputable section
universe u w
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual tensor span with its Cartan factor bounded in degree. -/
def cartanSymmetricTensorDegreeFiltration (τ : ContinuousCompactRep K n) (d : ℕ) :
    Submodule ℂ (CartanSymmetricCovariantModule K n τ) :=
  Submodule.span ℂ {x | ∃ P ∈ cartanSymmetricDegreeFiltration K n d,
    ∃ v : Fin τ.dim → ℂ, P ⊗ₜ[ℂ] v = x}

theorem tmul_mem_cartanSymmetricTensorDegreeFiltration
    (τ : ContinuousCompactRep K n) {d : ℕ} {P : CartanSymmetricAlgebra K n}
    (hP : P ∈ cartanSymmetricDegreeFiltration K n d) (v : Fin τ.dim → ℂ) :
    P ⊗ₜ[ℂ] v ∈ cartanSymmetricTensorDegreeFiltration K n τ d :=
  Submodule.subset_span ⟨P, hP, v, rfl⟩

theorem cartanSymmetricDegreeFiltration_mono :
    Monotone (cartanSymmetricDegreeFiltration K n) := by
  intro d e h
  apply Submodule.span_mono
  rintro P ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

theorem cartanSymmetricTensorDegreeFiltration_mono (τ : ContinuousCompactRep K n) :
    Monotone (cartanSymmetricTensorDegreeFiltration K n τ) := by
  intro d e h
  apply Submodule.span_mono
  rintro x ⟨P, hP, v, rfl⟩
  exact ⟨P, cartanSymmetricDegreeFiltration_mono K n h hP, v, rfl⟩

/-- Compact conjugation preserves the actual Cartan monomial bound. -/
theorem cartanSymmetricConjugation_mem_degreeFiltration
    (k : standardInfiniteCompact K n) {d : ℕ} {P : CartanSymmetricAlgebra K n}
    (hP : P ∈ cartanSymmetricDegreeFiltration K n d) :
    cartanSymmetricConjugation K n k P ∈ cartanSymmetricDegreeFiltration K n d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    have heq : cartanSymmetricConjugation K n k ((l.map (SymmetricAlgebra.ι ℂ _)).prod) =
        ((l.map (cartanComplexConjugation K n k)).map (SymmetricAlgebra.ι ℂ _)).prod := by
      simp only [map_list_prod, List.map_map, Function.comp_def,
        cartanSymmetricConjugation_ι]
    rw [heq]
    exact Submodule.subset_span ⟨l.map (cartanComplexConjugation K n k),
      by simpa using hl, rfl⟩
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
    simpa only [map_add] using (cartanSymmetricDegreeFiltration K n d).add_mem ihP ihQ
  | smul z P hP ih =>
    simpa only [map_smul] using (cartanSymmetricDegreeFiltration K n d).smul_mem z ih

/-- The diagonal compact action preserves the bounded tensor span. -/
theorem cartanSymmetricCovariantRepresentation_mem_degreeFiltration
    (τ : ContinuousCompactRep K n) (k : standardInfiniteCompact K n) {d : ℕ}
    {x : CartanSymmetricCovariantModule K n τ}
    (hx : x ∈ cartanSymmetricTensorDegreeFiltration K n τ d) :
    cartanSymmetricCovariantRepresentation K n τ k x ∈
      cartanSymmetricTensorDegreeFiltration K n τ d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, hP, v, rfl⟩ := hx
    rw [cartanSymmetricCovariantRepresentation_tmul]
    exact tmul_mem_cartanSymmetricTensorDegreeFiltration K n τ
      (cartanSymmetricConjugation_mem_degreeFiltration K n k hP) _
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using
      (cartanSymmetricTensorDegreeFiltration K n τ d).add_mem ihx ihy
  | smul z x hx ih =>
    simpa only [map_smul] using
      (cartanSymmetricTensorDegreeFiltration K n τ d).smul_mem z ih

section Module

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
  [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

/-- Act by the symmetrized Cartan factor on the image of the representation factor. -/
def cartanTensorAction (τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) :
    CartanSymmetricCovariantModule K n τ →ₗ[ℂ] V :=
  TensorProduct.lift
    (((Algebra.lsmul ℂ ℂ V).toLinearMap.comp
      (cartanSymmetricAlgebraSymmetrize K n)).compl₂ j)

@[simp]
theorem cartanTensorAction_tmul (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (P : CartanSymmetricAlgebra K n) (v : Fin τ.dim → ℂ) :
    cartanTensorAction K n τ j (P ⊗ₜ[ℂ] v) =
      cartanSymmetricAlgebraSymmetrize K n P • j v := rfl

/-- The image of a bounded tensor span is exactly the bounded Cartan action span. -/
theorem cartanTensorAction_map_degreeFiltration (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (d : ℕ) :
    (cartanSymmetricTensorDegreeFiltration K n τ d).map (cartanTensorAction K n τ j) =
      cartanSymmetrizationSpan K n d • LinearMap.range j := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro x ⟨P, hP, v, rfl⟩
    change cartanTensorAction K n τ j (P ⊗ₜ[ℂ] v) ∈
      cartanSymmetrizationSpan K n d • LinearMap.range j
    rw [cartanTensorAction_tmul]
    exact Submodule.smul_mem_smul ⟨P, hP, rfl⟩ ⟨v, rfl⟩
  · apply Submodule.smul_le.mpr
    rintro a ⟨P, hP, rfl⟩ w ⟨v, rfl⟩
    exact ⟨P ⊗ₜ[ℂ] v, tmul_mem_cartanSymmetricTensorDegreeFiltration K n τ hP v, rfl⟩

/-- Compact stability of the chosen range identifies its filtered orbit with
the image of actual bounded Cartan tensors. -/
theorem cartanTensorAction_map_degreeFiltration_eq (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (hj : ∀ X : CompactComplexLieAlgebra K n, ∀ w ∈ LinearMap.range j,
      compactEnvelopingGenerator K n X • w ∈ LinearMap.range j) (d : ℕ) :
    (cartanSymmetricTensorDegreeFiltration K n τ d).map (cartanTensorAction K n τ j) =
      envelopingDegreeFiltration K n d • LinearMap.range j := by
  rw [cartanTensorAction_map_degreeFiltration,
    cartanSymmetrizationSpan_smul_eq K n (LinearMap.range j) hj]

/-- Compatible compact actions make the actual tensor-action map equivariant. -/
theorem cartanTensorAction_equivariant (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (k : standardInfiniteCompact K n) (x : CartanSymmetricCovariantModule K n τ) :
    cartanTensorAction K n τ j (cartanSymmetricCovariantRepresentation K n τ k x) =
      ρ k (cartanTensorAction K n τ j x) := by
  induction x using TensorProduct.inductionOn with
  | tmul P v =>
    simp only [cartanSymmetricCovariantRepresentation_tmul, cartanTensorAction_tmul,
      hρ, hj, cartanSymmetricAlgebraSymmetrize_conjugation]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

end Module

end Langlands.Global.ArchimedeanGL
