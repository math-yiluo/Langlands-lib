import Langlands.Algebra.ProjectiveTensorCoefficients
import Langlands.RingTheory.Smooth.SectionJetBaseChange
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FiniteType

/-! # Finite-jet detection near a smooth section -/

noncomputable section

universe u v w

set_option autoImplicit false

open scoped TensorProduct

namespace Algebra.SectionJet

open Langlands.Algebra.ProjectiveTensorCoefficients

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  (ε : B →ₐ[R] R) (J : Ideal B)

/-- The ideal of scalar coefficients of the image of `J` in the order-`n` section jet. -/
def jetCoefficientIdeal (n : ℕ) : Ideal R :=
  Ideal.span {r | ∃ b ∈ J, ∃ φ : Quotient ε n →ₗ[R] R,
    φ (Ideal.Quotient.mk _ b) = r}

theorem jetCoefficientIdeal_monotone : Monotone (jetCoefficientIdeal ε J) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [jetCoefficientIdeal, Ideal.span_le]
  rintro r ⟨b, hb, φ, rfl⟩
  apply Ideal.subset_span
  exact ⟨b, hb, φ.comp (truncate ε n).toLinearMap, rfl⟩

/-- Killing the coefficient ideal is equivalent to killing `J` in the base-changed jet. -/
theorem jetCoefficientIdeal_le_ker_iff [FormallySmooth R B] [FiniteType R B]
    (S : Type w) [CommRing S] [Algebra R S] (n : ℕ) :
    jetCoefficientIdeal ε J n ≤ RingHom.ker (algebraMap R S) ↔
      ∀ b ∈ J, (1 ⊗ₜ[R] Ideal.Quotient.mk _ b : S ⊗[R] Quotient ε n) = 0 := by
  rw [jetCoefficientIdeal, Ideal.span_le]
  constructor
  · intro h b hb
    apply (eq_zero_iff_contract _).mpr
    intro φ
    rw [contract_tmul, Algebra.smul_def, mul_one]
    exact h ⟨b, hb, φ, rfl⟩
  · rintro h r ⟨b, hb, φ, rfl⟩
    apply RingHom.mem_ker.mpr
    have hφ := congrArg (contract (M := S) φ) (h b hb)
    simpa only [contract_tmul, Algebra.smul_def, mul_one, map_zero] using hφ

private theorem exists_common_annihilator {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) : ∃ r ∈ I, ∀ x ∈ (⨅ n : ℕ, I ^ n : Ideal A), r * x = x := by
  let N : Ideal A := ⨅ n : ℕ, I ^ n
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (N : Submodule A A)
  have hN (n : ℕ) : (I ^ n • ⊤ ⊓ N : Submodule A A) = N := by
    apply inf_eq_right.mpr
    rw [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one]
    exact iInf_le (fun n : ℕ => I ^ n) n
  have he := hk (k + 1) (Nat.le_succ k)
  rw [hN, hN, Nat.add_sub_cancel_left, pow_one] at he
  exact Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N
    (IsNoetherian.noetherian _) (le_of_eq he)

/-- Over a Noetherian base, one order of the jet of a section of a smooth morphism
detects vanishing on a principal neighborhood of the section. The order is
uniform for all changes of coefficient ring, including nonflat changes. -/
theorem exists_order_of_vanishing_near_section
    [IsNoetherianRing R] [FormallySmooth R B] [FiniteType R B] :
    ∃ n : ℕ, ∀ (S : Type w) [CommRing S] [Algebra R S],
      (∀ b ∈ J, (1 ⊗ₜ[R] Ideal.Quotient.mk _ b : S ⊗[R] Quotient ε n) = 0) →
      ∃ f : S ⊗[R] B, baseChangeAugmentation ε S f = 1 ∧
        ∀ b ∈ J, f * (1 ⊗ₜ[R] b) = 0 := by
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R))
    ⟨fun n => (jetCoefficientIdeal ε J n : Submodule R R), jetCoefficientIdeal_monotone ε J⟩
  let K := jetCoefficientIdeal ε J n
  let S₀ := R ⧸ K
  let ε₀ := baseChangeAugmentation ε S₀
  let I₀ := RingHom.ker ε₀
  have hcoeff (m : ℕ) : jetCoefficientIdeal ε J m ≤ K := by
    rcases le_total m n with h | h
    · exact jetCoefficientIdeal_monotone ε J h
    · exact le_of_eq (hn m h).symm
  have hpow (b : B) (hb : b ∈ J) : (1 ⊗ₜ[R] b : S₀ ⊗[R] B) ∈ ⨅ m : ℕ, I₀ ^ m := by
    rw [Submodule.mem_iInf]
    intro m
    cases m with
    | zero => simp
    | succ m =>
      have hle : jetCoefficientIdeal ε J m ≤ RingHom.ker (algebraMap R S₀) := by
        change jetCoefficientIdeal ε J m ≤ RingHom.ker (Ideal.Quotient.mk K)
        rw [Ideal.mk_ker]
        exact hcoeff m
      have hz := congrArg (baseChangeEquiv ε S₀ m)
        ((jetCoefficientIdeal_le_ker_iff ε J S₀ m).mp hle b hb)
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [baseChangeEquiv_tmul_mk, map_zero] using hz
  let : IsNoetherianRing (S₀ ⊗[R] B) := Algebra.FiniteType.isNoetherianRing S₀ _
  obtain ⟨r, hr, hkill⟩ := exists_common_annihilator I₀
  let f₀ : S₀ ⊗[R] B := 1 - r
  have hf₀ : ε₀ f₀ = 1 := by
    change ε₀ (1 - r) = 1
    rw [map_sub, map_one, show ε₀ r = 0 from hr, sub_zero]
  have hvanish (b : B) (hb : b ∈ J) : f₀ * (1 ⊗ₜ[R] b) = 0 := by
    dsimp only [f₀]
    rw [sub_mul, one_mul, hkill _ (hpow b hb), sub_self]
  refine ⟨n, fun S _ _ h => ?_⟩
  let g : S₀ →ₐ[R] S :=
    Ideal.Quotient.liftₐ K (Algebra.ofId R S)
      ((jetCoefficientIdeal_le_ker_iff ε J S n).mpr h)
  let gB := Algebra.TensorProduct.map g (AlgHom.id R B)
  have haug (z : S₀ ⊗[R] B) : baseChangeAugmentation ε S (gB z) = g (ε₀ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul s b => simp [gB, ε₀, g.commutes]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨gB f₀, by rw [haug, hf₀, map_one], fun b hb => ?_⟩
  simpa only [map_mul, gB, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply,
    map_zero] using congrArg gB (hvanish b hb)

end Algebra.SectionJet
