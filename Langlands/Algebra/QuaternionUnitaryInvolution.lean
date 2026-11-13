import Langlands.Algebra.UnitaryInvolutionNorm
import Langlands.Algebra.QuaternionCommutator

/-!
# The canonical involution of a quaternion division algebra and unitary involutions

For a central division algebra `D` of reduced degree `2` over a field `L`, the canonical
involution `γ x = Trd x - x` reverses products. If `τ` is a unitary involution of `D`
relative to `σ`, then `τ` commutes with `γ`, and `β = τ ∘ γ` is a ring automorphism of `D`
of order dividing two that acts on `L` through `σ`.
-/

noncomputable section

namespace Langlands.UnitaryInvolution

universe u

open Langlands.CentralDivision Langlands.CentralSimple
open scoped TensorProduct

section Quaternion

variable {L D : Type u} [Field L] [DivisionRing D] [Algebra L D] [FiniteDimensional L D]
  [Algebra.IsCentral L D]

/-- The reduced norm as a function on the division algebra. -/
abbrev nrd (L : Type u) {D : Type u} [Field L] [DivisionRing D] [Algebra L D]
    [FiniteDimensional L D] [Algebra.IsCentral L D] (x : D) : L :=
  reducedNorm L D L (1 ⊗ₜ[L] x)

theorem nrd_mul (x y : D) : nrd L (x * y) = nrd L x * nrd L y := by
  rw [nrd, nrd, nrd, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem nrd_one : nrd L (1 : D) = 1 := by
  rw [nrd, ← Algebra.TensorProduct.one_def, map_one]

theorem nrd_zero : nrd L (0 : D) = 0 := by
  rw [nrd, TensorProduct.tmul_zero, map_zero]

theorem nrd_ne_zero {x : D} (hx : x ≠ 0) : nrd L x ≠ 0 := by
  intro h
  have := nrd_mul (L := L) x x⁻¹
  rw [mul_inv_cancel₀ hx, nrd_one, h, zero_mul] at this
  exact one_ne_zero this

theorem nrd_algebraMap (c : L) : nrd L (algebraMap L D c) = c ^ reducedDegree L D := by
  rw [nrd, ← reducedNorm_scalar L D L c]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-- The canonical involution `x ↦ Trd x - x`. -/
def gamma (L : Type u) {D : Type u} [Field L] [DivisionRing D] [Algebra L D]
    [FiniteDimensional L D] [Algebra.IsCentral L D] (x : D) : D :=
  algebraMap L D (reducedTrace L D x) - x

variable (hd : reducedDegree L D = 2)
include hd

theorem cayleyHamilton (x : D) :
    x ^ 2 - algebraMap L D (reducedTrace L D x) * x + algebraMap L D (nrd L x) = 0 :=
  sq_sub_reducedTrace_add_reducedNorm L D hd x

theorem mul_gamma (x : D) : x * gamma L x = algebraMap L D (nrd L x) := by
  have h := cayleyHamilton hd x
  rw [sq] at h
  rw [gamma, mul_sub, ← Algebra.commutes, ← sub_eq_zero, ← neg_eq_zero, ← h]
  abel

theorem gamma_mul_self (x : D) : gamma L x * x = algebraMap L D (nrd L x) := by
  have h := cayleyHamilton hd x
  rw [sq] at h
  rw [gamma, sub_mul, ← sub_eq_zero, ← neg_eq_zero, ← h]
  abel

theorem reducedTrace_algebraMap (c : L) : reducedTrace L D (algebraMap L D c) = 2 * c := by
  rw [Algebra.algebraMap_eq_smul_one, reducedTrace_smul, reducedTrace_one L D hd, mul_comm]

omit hd in
theorem reducedTrace_zero : reducedTrace L D (0 : D) = 0 := by
  have := reducedTrace_smul L D 0 (0 : D)
  rwa [zero_smul, zero_mul] at this

omit hd in
theorem gamma_zero : gamma L (0 : D) = 0 := by
  rw [gamma, reducedTrace_zero, map_zero, sub_zero]

theorem gamma_algebraMap (c : L) : gamma L (algebraMap L D c) = algebraMap L D c := by
  rw [gamma, reducedTrace_algebraMap hd, map_mul, map_ofNat, two_mul, add_sub_cancel_right]

omit hd in
theorem gamma_add (x y : D) : gamma L (x + y) = gamma L x + gamma L y := by
  rw [gamma, gamma, gamma, reducedTrace_add, map_add]
  abel

theorem gamma_gamma (x : D) : gamma L (gamma L x) = x := by
  have ht : reducedTrace L D (gamma L x) = reducedTrace L D x := by
    rw [gamma, reducedTrace_sub, reducedTrace_algebraMap hd]
    ring
  rw [gamma, ht, gamma, sub_sub_cancel]

theorem gamma_eq_nrd_mul_inv {x : D} (hx : x ≠ 0) :
    gamma L x = algebraMap L D (nrd L x) * x⁻¹ := by
  calc gamma L x = x⁻¹ * (x * gamma L x) := by rw [inv_mul_cancel_left₀ hx]
    _ = x⁻¹ * algebraMap L D (nrd L x) := by rw [mul_gamma hd]
    _ = algebraMap L D (nrd L x) * x⁻¹ := (Algebra.commutes _ _).symm

theorem gamma_mul (x y : D) : gamma L (x * y) = gamma L y * gamma L x := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, gamma_zero, mul_zero]
  by_cases hy : y = 0
  · rw [hy, mul_zero, gamma_zero, zero_mul]
  rw [gamma_eq_nrd_mul_inv hd (mul_ne_zero hx hy), gamma_eq_nrd_mul_inv hd hx,
    gamma_eq_nrd_mul_inv hd hy, nrd_mul, map_mul, mul_inv_rev, mul_assoc, mul_assoc,
    ← mul_assoc y⁻¹, ← Algebra.commutes, mul_assoc]
  exact Algebra.left_comm _ _ _

theorem nrd_gamma (x : D) : nrd L (gamma L x) = nrd L x := by
  by_cases hx : x = 0
  · rw [hx, gamma_zero]
  have h := congrArg (nrd L) (mul_gamma hd x)
  rw [nrd_mul, nrd_algebraMap, hd, sq] at h
  exact mul_left_cancel₀ (nrd_ne_zero hx) h

end Quaternion


/-- The `σ`-semilinear ring automorphism `β = τ ∘ γ`. -/
def beta (L : Type u) {D : Type u} [Field L] [DivisionRing D] [Algebra L D]
    [FiniteDimensional L D] [Algebra.IsCentral L D] (τ : D → D) (x : D) : D :=
  τ (gamma L x)

section Unitary

variable {L D : Type u} [Field L] [DivisionRing D] [Algebra L D] [FiniteDimensional L D]
  [Algebra.IsCentral L D] (hd : reducedDegree L D = 2) {σ : L →+* L} {τ : D → D}
  (hτ : IsUnitaryInvolution (⇑σ) τ)
include hd hτ

theorem tau_cayleyHamilton (x : D) :
    τ x ^ 2 - algebraMap L D (σ (reducedTrace L D x)) * τ x +
      algebraMap L D (σ (nrd L x)) = 0 := by
  have h := congrArg τ (cayleyHamilton hd x)
  rw [tau_zero hτ] at h
  rw [← h, hτ.1, tau_sub hτ, tau_pow hτ, tau_mul hτ, tau_algebraMap hτ, tau_algebraMap hτ,
    Algebra.commutes]

theorem reducedTrace_tau_and_nrd_tau (x : D) :
    reducedTrace L D (τ x) = σ (reducedTrace L D x) ∧ nrd L (τ x) = σ (nrd L x) := by
  have h1 := tau_cayleyHamilton hd hτ x
  have h2 := cayleyHamilton hd (τ x)
  have h3 : algebraMap L D (reducedTrace L D (τ x) - σ (reducedTrace L D x)) * τ x =
      algebraMap L D (nrd L (τ x) - σ (nrd L x)) := by
    have h0 := sub_eq_zero.mpr (h1.trans h2.symm)
    rw [← sub_eq_zero, ← h0]
    simp only [map_sub, sub_mul]
    abel
  by_cases hc : reducedTrace L D (τ x) - σ (reducedTrace L D x) = 0
  · have he : algebraMap L D (nrd L (τ x) - σ (nrd L x)) = algebraMap L D 0 := by
      rw [← h3, hc, map_zero, zero_mul]
    exact ⟨sub_eq_zero.mp hc, sub_eq_zero.mp ((algebraMap L D).injective he)⟩
  · exfalso
    apply hc
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : L, x = algebraMap L D ℓ := by
      refine ⟨σ ((reducedTrace L D (τ x) - σ (reducedTrace L D x))⁻¹ *
        (nrd L (τ x) - σ (nrd L x))), ?_⟩
      rw [← tau_algebraMap hτ, map_mul, ← h3, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc,
        map_one, one_mul, tau_tau hτ]
    rw [hℓ, tau_algebraMap hτ, reducedTrace_algebraMap hd, reducedTrace_algebraMap hd, map_mul,
      map_ofNat, sub_self]

theorem reducedTrace_tau (x : D) : reducedTrace L D (τ x) = σ (reducedTrace L D x) :=
  (reducedTrace_tau_and_nrd_tau hd hτ x).1

theorem nrd_tau (x : D) : nrd L (τ x) = σ (nrd L x) :=
  (reducedTrace_tau_and_nrd_tau hd hτ x).2

theorem gamma_tau (x : D) : gamma L (τ x) = τ (gamma L x) := by
  rw [gamma, gamma, tau_sub hτ, tau_algebraMap hτ, reducedTrace_tau hd hτ]


omit hd in
theorem beta_add (x y : D) : beta L τ x + beta L τ y = beta L τ (x + y) := by
  rw [beta, beta, beta, gamma_add, hτ.1]

theorem beta_mul (x y : D) : beta L τ (x * y) = beta L τ x * beta L τ y := by
  rw [beta, beta, beta, gamma_mul hd, tau_mul hτ]

theorem beta_algebraMap (c : L) : beta L τ (algebraMap L D c) = algebraMap L D (σ c) := by
  rw [beta, gamma_algebraMap hd, tau_algebraMap hτ]

theorem beta_beta (x : D) : beta L τ (beta L τ x) = x := by
  rw [beta, beta, gamma_tau hd hτ, tau_tau hτ, gamma_gamma hd]

theorem nrd_beta (x : D) : nrd L (beta L τ x) = σ (nrd L x) := by
  rw [beta, nrd_tau hd hτ, nrd_gamma hd]

theorem reducedTrace_beta (x : D) :
    reducedTrace L D (beta L τ x) = σ (reducedTrace L D x) := by
  rw [beta, reducedTrace_tau hd hτ, gamma, reducedTrace_sub, reducedTrace_algebraMap hd]
  ring_nf

/-- `β` as a ring endomorphism. -/
def betaHom : D →+* D where
  toFun := beta L τ
  map_one' := by simpa using beta_algebraMap hd hτ 1
  map_mul' := beta_mul hd hτ
  map_zero' := by simpa using beta_algebraMap hd hτ 0
  map_add' x y := (beta_add hτ x y).symm

@[simp] theorem betaHom_apply (x : D) : betaHom hd hτ x = beta L τ x := rfl

end Unitary

end Langlands.UnitaryInvolution
