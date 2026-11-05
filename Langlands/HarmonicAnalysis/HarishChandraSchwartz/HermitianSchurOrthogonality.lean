import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality
import Langlands.Representation.Plancherel.CoefficientTensorForm

/-! # Hermitian Schur orthogonality for coefficient tensors

Waldspurger, proof of Proposition VII.2.1, case `M = G` (printed p. 318): "Des formules analogues
à III.1 (2) et (3) (pour des produits hermitiens) impliquent que `(E ψ', E ψ_ω)_{A_G\G} = 0` si
`ω' ≄ ω`, `(ψ', ψ_ω)` si `ω' ≃ ω`." For smooth representations `P₁`, `P₂` of `G` on which a
normal central subgroup `A` acts by the same character, and coefficient tensors
`ψᵢ ∈ Pᵢ ⊗ P̃ᵢ` with coefficients `E ψᵢ`, this module defines
`(E ψ₂, E ψ₁)_{G/A} = ∫_{G/A} conj((E ψ₂)(g)) (E ψ₁)(g) dg` and proves both formulas for
irreducible representations square integrable modulo `A`: the pairing vanishes for inequivalent
`P₁`, `P₂`, and for `P₁ = P₂ = P` it is `d(P)⁻¹ (v₂, v₁)(ℓ₂, ℓ₁)`, the form of V.2 on `P ⊗ P̃`.
-/

noncomputable section

universe u v w

open MeasureTheory
open scoped TensorProduct ComplexConjugate
open Langlands.Plancherel (CoefficientTensor coefficientTensorMap coefficientTensorMap_tmul
  coefficientTensorInvariantForm coefficientTensorInvariantForm_inner_tmul
  IsSquareIntegrableModCentralSubgroup coefficientTensorCongr coefficientTensorMap_congr)

namespace Langlands.HarishChandraSchwartz

section Function

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Subgroup G)
  {χ : A →* ℂˣ}

/-- A coefficient of a representation on which `A` acts by `χ` transforms by `χ` under right
translation by `A`. -/
theorem coefficientTensorMap_mul_of_central {P : SmoothRep.{0, u, v} ℂ G}
    (h : ∀ (a : A) (x : P), P.representation a x = (χ a : ℂ) • x) (ψ : CoefficientTensor P)
    (g : G) (a : A) :
    coefficientTensorMap P ψ (g * a) = (χ a : ℂ) * coefficientTensorMap P ψ g := by
  induction ψ using TensorProduct.inductionOn with
  | tmul x ℓ =>
    rw [coefficientTensorMap_tmul, coefficientTensorMap_tmul, map_mul, Module.End.mul_apply, h,
      map_smul, map_smul, smul_eq_mul]
  | add x y hx hy =>
    simp only [map_add, LocallyConstant.coe_add, Pi.add_apply, hx, hy, mul_add]

variable {P₁ : SmoothRep.{0, u, v} ℂ G} {P₂ : SmoothRep.{0, u, w} ℂ G}

/-- `g ↦ conj((E ψ₂)(g)) (E ψ₁)(g)`, the integrand of the Hermitian product of two
coefficients. -/
def hermitianCoefficientFun (ψ₂ : CoefficientTensor P₂) (ψ₁ : CoefficientTensor P₁) (g : G) :
    ℂ :=
  conj (coefficientTensorMap P₂ ψ₂ g) * coefficientTensorMap P₁ ψ₁ g

variable (h₁ : ∀ (a : A) (x : P₁), P₁.representation a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : P₂), P₂.representation a x = (χ a : ℂ) • x)
  (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1)

include h₁ h₂ hu in
theorem hermitianCoefficientFun_mul (ψ₂ : CoefficientTensor P₂) (ψ₁ : CoefficientTensor P₁)
    (g : G) (a : A) :
    hermitianCoefficientFun ψ₂ ψ₁ (g * a) = hermitianCoefficientFun ψ₂ ψ₁ g := by
  unfold hermitianCoefficientFun
  rw [coefficientTensorMap_mul_of_central A h₂, coefficientTensorMap_mul_of_central A h₁, map_mul]
  have hχ : conj (χ a : ℂ) * (χ a : ℂ) = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu a]
    simp
  calc conj (χ a : ℂ) * conj (coefficientTensorMap P₂ ψ₂ g) *
        ((χ a : ℂ) * coefficientTensorMap P₁ ψ₁ g) =
      (conj (χ a : ℂ) * (χ a : ℂ)) *
        (conj (coefficientTensorMap P₂ ψ₂ g) * coefficientTensorMap P₁ ψ₁ g) := by ring
    _ = _ := by rw [hχ, one_mul]

/-- The Hermitian integrand as a function on `G/A`; it is well defined because `P₁` and `P₂`
act on `A` by the same unitary character. -/
def hermitianCoefficientIntegrand (ψ₂ : CoefficientTensor P₂) (ψ₁ : CoefficientTensor P₁) :
    G ⧸ A → ℂ :=
  Quotient.lift (hermitianCoefficientFun ψ₂ ψ₁) (by
    intro x y hxy
    have hz : x⁻¹ * y ∈ A := QuotientGroup.leftRel_apply.mp hxy
    have h := hermitianCoefficientFun_mul A h₁ h₂ hu ψ₂ ψ₁ x ⟨x⁻¹ * y, hz⟩
    simpa using h.symm)

theorem hermitianCoefficientIntegrand_mk (ψ₂ : CoefficientTensor P₂) (ψ₁ : CoefficientTensor P₁)
    (g : G) :
    hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁ (QuotientGroup.mk g) =
      conj (coefficientTensorMap P₂ ψ₂ g) * coefficientTensorMap P₁ ψ₁ g :=
  rfl

theorem hermitianCoefficientIntegrand_add_left (ψ₂ ψ₂' : CoefficientTensor P₂)
    (ψ₁ : CoefficientTensor P₁) :
    hermitianCoefficientIntegrand A h₁ h₂ hu (ψ₂ + ψ₂') ψ₁ =
      hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁ +
        hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂' ψ₁ := by
  funext q
  induction q using QuotientGroup.induction_on with
  | H g =>
    simp only [Pi.add_apply, hermitianCoefficientIntegrand_mk, map_add, LocallyConstant.coe_add,
      Pi.add_apply]
    ring

theorem hermitianCoefficientIntegrand_add_right (ψ₂ : CoefficientTensor P₂)
    (ψ₁ ψ₁' : CoefficientTensor P₁) :
    hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ (ψ₁ + ψ₁') =
      hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁ +
        hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁' := by
  funext q
  induction q using QuotientGroup.induction_on with
  | H g =>
    simp only [Pi.add_apply, hermitianCoefficientIntegrand_mk, map_add, LocallyConstant.coe_add,
      Pi.add_apply]
    ring

/-- On pure tensors, with `ℓ₂ = b₂(w₂, -)`, the Hermitian integrand is Waldspurger's
`I(v₁, ℓ₁, w₂, b₂(v₂, -))` integrand of III.1. -/
theorem hermitianCoefficientIntegrand_tmul (b₂ : InvariantPositiveForm P₂.representation)
    (hP₂ : IsSmooth P₂.representation) (v₂ w₂ : P₂) (v₁ : P₁)
    (ℓ₁ : SmoothDual P₁.representation) :
    hermitianCoefficientIntegrand A h₁ h₂ hu (v₂ ⊗ₜ[ℂ] b₂.toSmoothDual hP₂ w₂) (v₁ ⊗ₜ[ℂ] ℓ₁) =
      orthogonalityIntegrand A h₁ h₂ v₁ ℓ₁.val w₂ (b₂.toSmoothDual hP₂ v₂).val := by
  funext q
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [hermitianCoefficientIntegrand_mk, orthogonalityIntegrand_mk, coefficientTensorMap_tmul,
      coefficientTensorMap_tmul]
    change conj (b₂.inner w₂ (P₂.representation g v₂)) * ℓ₁.val (P₁.representation g v₁) =
      ℓ₁.val (P₁.representation g v₁) * b₂.inner v₂ (P₂.representation g⁻¹ w₂)
    rw [b₂.conj_inner_symm, ← b₂.invariant g⁻¹ (P₂.representation g v₂) w₂,
      Representation.inv_self_apply, mul_comm]

end Function

section Pairing

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {χ : A →* ℂˣ} {P₁ : SmoothRep.{0, u, v} ℂ G} {P₂ : SmoothRep.{0, u, w} ℂ G}
  (h₁ : ∀ (a : A) (x : P₁), P₁.representation a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : P₂), P₂.representation a x = (χ a : ℂ) • x)
  (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1)

/-- The Hermitian product `(E ψ₂, E ψ₁)_{G/A} = ∫_{G/A} conj((E ψ₂)(g)) (E ψ₁)(g) dg`. -/
def hermitianCoefficientPairing (ψ₂ : CoefficientTensor P₂) (ψ₁ : CoefficientTensor P₁) : ℂ :=
  ∫ q, hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁ q ∂μ

include hcof in
/-- For representations square integrable modulo `A`, with `P₂` unitarizable, the Hermitian
integrand is integrable on `G/A`. -/
theorem integrable_hermitianCoefficientIntegrand
    (hsq₁ : IsSquareIntegrableModCentralSubgroup A hA P₁.representation μ)
    (hsq₂ : IsSquareIntegrableModCentralSubgroup A hA P₂.representation μ)
    (b₂ : InvariantPositiveForm P₂.representation) (ψ₂ : CoefficientTensor P₂)
    (ψ₁ : CoefficientTensor P₁) :
    Integrable (hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁) μ := by
  induction ψ₂ using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [hermitianCoefficientIntegrand_add_left]
    exact hx.add hy
  | tmul v₂ ℓ₂ =>
    obtain ⟨w₂, rfl⟩ := (b₂.smoothDualEquiv hcof hsq₂.1).surjective ℓ₂
    induction ψ₁ using TensorProduct.inductionOn with
    | add x y hx hy =>
      rw [hermitianCoefficientIntegrand_add_right]
      exact hx.add hy
    | tmul v₁ ℓ₁ =>
      rw [InvariantPositiveForm.smoothDualEquiv_apply,
        hermitianCoefficientIntegrand_tmul A h₁ h₂ hu b₂ hsq₂.1.1]
      exact integrable_orthogonalityIntegrand A hA μ h₁ h₂ hsq₁ hsq₂ v₁ ℓ₁ w₂
        (b₂.toSmoothDual hsq₂.1.1 v₂)

include hcof in
/-- **Hermitian analogue of III.1 (2)**: if `P₁` and `P₂` are irreducible, square integrable
modulo `A` and inequivalent, then `(E ψ₂, E ψ₁)_{G/A} = 0` for all coefficient tensors. -/
theorem hermitianCoefficientPairing_eq_zero
    (hsq₁ : IsSquareIntegrableModCentralSubgroup A hA P₁.representation μ)
    (hsq₂ : IsSquareIntegrableModCentralSubgroup A hA P₂.representation μ)
    (hi₁ : P₁.representation.IsIrreducible) (hi₂ : P₂.representation.IsIrreducible)
    (hne : IsEmpty (P₁.representation.Equiv P₂.representation)) (ψ₂ : CoefficientTensor P₂)
    (ψ₁ : CoefficientTensor P₁) :
    hermitianCoefficientPairing A μ h₁ h₂ hu ψ₂ ψ₁ = 0 := by
  obtain ⟨b₂⟩ := isUnitarizable_of_isSquareIntegrable A hA μ h₂ hcof hsq₂ hi₂
  have hint := integrable_hermitianCoefficientIntegrand A hA μ hcof h₁ h₂ hu hsq₁ hsq₂ b₂
  induction ψ₂ using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [hermitianCoefficientPairing, hermitianCoefficientIntegrand_add_left,
      integral_add' (hint x ψ₁) (hint y ψ₁)]
    rw [hermitianCoefficientPairing] at hx hy
    rw [hx, hy, add_zero]
  | tmul v₂ ℓ₂ =>
    obtain ⟨w₂, rfl⟩ := (b₂.smoothDualEquiv hcof hsq₂.1).surjective ℓ₂
    induction ψ₁ using TensorProduct.inductionOn with
    | add x y hx hy =>
      rw [hermitianCoefficientPairing, hermitianCoefficientIntegrand_add_right,
        integral_add' (hint _ x) (hint _ y)]
      rw [hermitianCoefficientPairing] at hx hy
      rw [hx, hy, add_zero]
    | tmul v₁ ℓ₁ =>
      rw [hermitianCoefficientPairing, InvariantPositiveForm.smoothDualEquiv_apply,
        hermitianCoefficientIntegrand_tmul A h₁ h₂ hu b₂ hsq₂.1.1]
      exact orthogonalityIntegral_eq_zero A hA μ h₁ h₂ hcof hsq₁ hsq₂ hi₁ hi₂ hne v₁ ℓ₁ w₂
        (b₂.toSmoothDual hsq₂.1.1 v₂)

end Pairing

section Equal

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {χ : A →* ℂˣ} {P : SmoothRep.{0, u, v} ℂ G}
  (h : ∀ (a : A) (x : P), P.representation a x = (χ a : ℂ) • x)
  (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1)

/-- **Hermitian analogue of III.1 (3)**: for an irreducible `P`, square integrable modulo `A`,
with formal degree `d = formalDegree`, and any positive invariant form `b` on `P`,
`(E ψ₂, E ψ₁)_{G/A} = d⁻¹ (ψ₂, ψ₁)`, where `( , )` is the tensor form
`(v₂ ⊗ ℓ₂, v₁ ⊗ ℓ₁) = b(v₂, v₁) (ℓ₂, ℓ₁)` of `coefficientTensorInvariantForm`. -/
theorem hermitianCoefficientPairing_eq_inner
    (hsq : IsSquareIntegrableModCentralSubgroup A hA P.representation μ)
    (hi : P.representation.IsIrreducible) (b : InvariantPositiveForm P.representation)
    (ψ₂ ψ₁ : CoefficientTensor P) :
    hermitianCoefficientPairing A μ h h hu ψ₂ ψ₁ =
      ((formalDegree A hA μ h hcof hsq hi : ℂ))⁻¹ *
        (coefficientTensorInvariantForm P hcof hsq.1 b).inner ψ₂ ψ₁ := by
  have hint := integrable_hermitianCoefficientIntegrand A hA μ hcof h h hu hsq hsq b
  let B := coefficientTensorInvariantForm P hcof hsq.1 b
  induction ψ₂ using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [hermitianCoefficientPairing, hermitianCoefficientIntegrand_add_left,
      integral_add' (hint x ψ₁) (hint y ψ₁)]
    rw [hermitianCoefficientPairing] at hx hy
    rw [hx, hy, B.add_left, mul_add]
  | tmul v₂ ℓ₂ =>
    obtain ⟨w₂, rfl⟩ := (b.smoothDualEquiv hcof hsq.1).surjective ℓ₂
    induction ψ₁ using TensorProduct.inductionOn with
    | add x y hx hy =>
      rw [hermitianCoefficientPairing, hermitianCoefficientIntegrand_add_right,
        integral_add' (hint _ x) (hint _ y)]
      rw [hermitianCoefficientPairing] at hx hy
      rw [hx, hy, InvariantPositiveForm.add_right, mul_add]
    | tmul v₁ ℓ₁ =>
      obtain ⟨w₁, rfl⟩ := (b.smoothDualEquiv hcof hsq.1).surjective ℓ₁
      rw [hermitianCoefficientPairing, InvariantPositiveForm.smoothDualEquiv_apply,
        hermitianCoefficientIntegrand_tmul A h h hu b hsq.1.1]
      change orthogonalityIntegral A μ h h v₁ _ w₂ _ = _
      rw [orthogonalityIntegral_eq_formalDegree A hA μ h hcof hsq hi,
        coefficientTensorInvariantForm_inner_tmul]
      -- `b(v₂, -)(v₁) = b(v₂, v₁)`, `ℓ₁(w₂) = b(w₁, w₂)`, and the dual form gives `b(w₁, w₂)`
      show _ * b.inner v₂ v₁ * b.inner w₁ w₂ =
        _ * (b.inner v₂ v₁ * b.inner ((b.smoothDualEquiv hcof hsq.1).symm
          (b.smoothDualEquiv hcof hsq.1 w₁)) ((b.smoothDualEquiv hcof hsq.1).symm
            (b.smoothDualEquiv hcof hsq.1 w₂)))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      ring

end Equal

section Equivalent

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {χ : A →* ℂˣ} {P₁ : SmoothRep.{0, u, v} ℂ G} {P₂ : SmoothRep.{0, u, w} ℂ G}
  (h₁ : ∀ (a : A) (x : P₁), P₁.representation a x = (χ a : ℂ) • x)
  (h₂ : ∀ (a : A) (x : P₂), P₂.representation a x = (χ a : ℂ) • x)
  (hu : ∀ a : A, ‖(χ a : ℂ)‖ = 1)

omit [A.Normal] [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)] in
/-- Transporting the second tensor along an equivalence `e : P₁ ≃ P₂` does not change the
Hermitian integrand, because `coefficientTensorCongr` preserves coefficients. -/
theorem hermitianCoefficientIntegrand_congr (e : P₁.representation.Equiv P₂.representation)
    (ψ₂ : CoefficientTensor P₂) (ψ₁ : CoefficientTensor P₁) :
    hermitianCoefficientIntegrand A h₁ h₂ hu ψ₂ ψ₁ =
      hermitianCoefficientIntegrand A h₂ h₂ hu ψ₂ (coefficientTensorCongr e ψ₁) := by
  funext q
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [hermitianCoefficientIntegrand_mk, hermitianCoefficientIntegrand_mk,
      coefficientTensorMap_congr]

/-- **Hermitian III.1 (3) for equivalent representations**: if `e : P₁ ≃ P₂` and `P₂` is
irreducible and square integrable modulo `A`, then
`(E ψ₂, E ψ₁)_{G/A} = d(P₂)⁻¹ (ψ₂, e_* ψ₁)` for the tensor form on `P₂ ⊗ P̃₂`, where `e_*` is the
transport `coefficientTensorCongr e`. -/
theorem hermitianCoefficientPairing_eq_inner_of_equiv
    (e : P₁.representation.Equiv P₂.representation)
    (hsq₂ : IsSquareIntegrableModCentralSubgroup A hA P₂.representation μ)
    (hi₂ : P₂.representation.IsIrreducible) (b₂ : InvariantPositiveForm P₂.representation)
    (ψ₂ : CoefficientTensor P₂) (ψ₁ : CoefficientTensor P₁) :
    hermitianCoefficientPairing A μ h₁ h₂ hu ψ₂ ψ₁ =
      ((formalDegree A hA μ h₂ hcof hsq₂ hi₂ : ℂ))⁻¹ *
        (coefficientTensorInvariantForm P₂ hcof hsq₂.1 b₂).inner ψ₂
          (coefficientTensorCongr e ψ₁) := by
  rw [hermitianCoefficientPairing, hermitianCoefficientIntegrand_congr A h₁ h₂ hu e]
  exact hermitianCoefficientPairing_eq_inner A hA μ hcof h₂ hu hsq₂ hi₂ b₂ ψ₂ _

end Equivalent

end Langlands.HarishChandraSchwartz
