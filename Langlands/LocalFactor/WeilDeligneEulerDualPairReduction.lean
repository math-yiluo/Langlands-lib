import Langlands.LocalFactor.WeilDeligneEulerStatement
import Langlands.LocalFactor.WeilDeligne
import Langlands.WeilDeligne.BlockDualProof

/-! # Dual pair-block Euler formulas from the ordinary formulas -/

noncomputable section

set_option maxHeartbeats 1000000

universe uK uG uV uW

open scoped TensorProduct BigOperators

namespace Langlands.FiniteRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- Twisting both factors scales the tensor action by the product character. -/
theorem tensor_twist_action (χ ψ : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) (g : G) :
    (tensor (twist χ A) (twist ψ B)).representation g =
      ((χ g : K) * (ψ g : K)) • (tensor A B).representation g := by
  change TensorProduct.map ((χ g : K) • A.representation g)
      ((ψ g : K) • B.representation g) =
    ((χ g : K) * (ψ g : K)) •
      TensorProduct.map (A.representation g) (B.representation g)
  calc
    _ = (χ g : K) •
        TensorProduct.map (A.representation g) ((ψ g : K) • B.representation g) :=
      TensorProduct.map_smul_left (χ g : K) (A.representation g)
        ((ψ g : K) • B.representation g)
    _ = (χ g : K) • ((ψ g : K) •
        TensorProduct.map (A.representation g) (B.representation g)) :=
      congrArg (fun f : Module.End K (A ⊗[K] B) => (χ g : K) • f)
        (TensorProduct.map_smul_right (ψ g : K) (A.representation g) (B.representation g))
    _ = _ := smul_smul _ _ _

/-- Inertia-trivial twists preserve the actual fixed subspace of the tensor. -/
def invariantsTensorTwistEquiv (χ ψ : G →* Kˣ)
    (I : Subgroup G) [I.Normal] (hχ : ∀ i : I, χ i = 1) (hψ : ∀ i : I, ψ i = 1)
    (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) :
    invariants I (tensor A B) ≃ₗ[K] invariants I (tensor (twist χ A) (twist ψ B)) where
  toFun x := ⟨x.val, fun i => by
    change (tensor (twist χ A) (twist ψ B)).representation i x.val = x.val
    rw [tensor_twist_action]
    rw [hχ i, hψ i, Units.val_one, one_mul, one_smul]
    exact x.property i⟩
  invFun x := ⟨x.val, fun i => by
    have h := x.property i
    change (tensor (twist χ A) (twist ψ B)).representation i x.val = x.val at h
    rw [tensor_twist_action] at h
    rw [hχ i, hψ i, Units.val_one, one_mul, one_smul] at h
    exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

/-- The operator on tensor invariants is scaled by both twisting characters. -/
theorem invariantsTensorTwist_conj (χ ψ : G →* Kˣ)
    (I : Subgroup G) [I.Normal] (hχ : ∀ i : I, χ i = 1) (hψ : ∀ i : I, ψ i = 1)
    (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) (g : G) (c : K) :
    (invariantsTensorTwistEquiv χ ψ I hχ hψ A B).conj
        ((c * ((χ g : K) * (ψ g : K))) • (invariants I (tensor A B)).representation g) =
      c • (invariants I (tensor (twist χ A) (twist ψ B))).representation g := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (c * ((χ g : K) * (ψ g : K))) • (tensor A B).representation g x.val =
    c • (tensor (twist χ A) (twist ψ B)).representation g x.val
  rw [tensor_twist_action]
  change (c * ((χ g : K) * (ψ g : K))) •
      (TensorProduct.map (A.representation g) (B.representation g) x.val) =
    c • (((χ g : K) * (ψ g : K)) •
      (TensorProduct.map (A.representation g) (B.representation g) x.val))
  exact (smul_smul _ _ _).symm

end Langlands.FiniteRepresentation

namespace Langlands.LocalFactor

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- Euler factors of a scalar operator on the twisted tensor fixed space. -/
theorem eulerPolynomial_invariantsTensorTwist (χ ψ : G →* Kˣ)
    (I : Subgroup G) [I.Normal] (hχ : ∀ i : I, χ i = 1) (hψ : ∀ i : I, ψ i = 1)
    (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) (g : G) (c : K) :
    eulerPolynomial
        (c • (FiniteRepresentation.invariants I
          (FiniteRepresentation.tensor (FiniteRepresentation.twist χ A)
            (FiniteRepresentation.twist ψ B))).representation g) =
      eulerPolynomial ((c * ((χ g : K) * (ψ g : K))) •
        (FiniteRepresentation.invariants I (FiniteRepresentation.tensor A B)).representation g) := by
  rw [← FiniteRepresentation.invariantsTensorTwist_conj χ ψ I hχ hψ A B g c,
    eulerPolynomial_conj]

private theorem dualPairTwist_scalar (u : Kˣ) (n m : ℕ)
    (j : Fin (min (n + 1) (m + 1))) :
    (u : K) ^ (n + m - j.val) *
        (((u ^ (1 - ((n + 1 : ℕ) : ℤ)) : Kˣ) : K) *
          ((u ^ (1 - ((m + 1 : ℕ) : ℤ)) : Kˣ) : K)) =
      (u : K) ^ (-(j.val : ℤ)) := by
  have hj : j.val ≤ n + m := by
    have := j.isLt
    have := Nat.min_le_left (n + 1) (m + 1)
    omega
  calc
    _ = ((u ^ ((n + m - j.val : ℕ) : ℤ) *
        u ^ (1 - ((n + 1 : ℕ) : ℤ)) *
        u ^ (1 - ((m + 1 : ℕ) : ℤ)) : Kˣ) : K) := by
      simp only [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, mul_assoc]
    _ = ((u ^ (-(j.val : ℤ)) : Kˣ) : K) := by
      congr 1
      rw [← zpow_add, ← zpow_add]
      congr 1
      rw [Nat.cast_sub hj]
      push_cast
      ring
    _ = _ := Units.val_zpow_eq_zpow_val _ _

/-- The dual pair-block formula follows from the ordinary pair-block formula. -/
def WDEulerDualPairBlockReductionStatement : Prop :=
  WDEulerPairBlockStatement.{uK, uG, max uK uV, max uK uW} →
    WDEulerDualPairBlockStatement.{uK, uG, uV, uW}

/-- Block duality changes the ordinary exponents `n+m-j` into `-j`. -/
theorem wdEulerDualPairBlock_of_pairBlock :
    WDEulerDualPairBlockReductionStatement.{uK, uG, uV, uW} := by
  intro h K _ _ G _ ν I _ hν Φ A B n m
  let χ : G →* Kˣ := ν ^ (1 - ((n + 1 : ℕ) : ℤ))
  let ψ : G →* Kˣ := ν ^ (1 - ((m + 1 : ℕ) : ℤ))
  have hχ : ∀ i : I, χ i = 1 := by
    intro i
    simp [χ, MonoidHom.zpow_apply, hν i]
  have hψ : ∀ i : I, ψ i = 1 := by
    intro i
    simp [ψ, MonoidHom.zpow_apply, hν i]
  let D := FiniteRepresentation.invariants I
    (FiniteRepresentation.tensor (FiniteRepresentation.dual A) (FiniteRepresentation.dual B))
  let T := FiniteRepresentation.invariants I
    (FiniteRepresentation.tensor (FiniteRepresentation.twist χ (FiniteRepresentation.dual A))
      (FiniteRepresentation.twist ψ (FiniteRepresentation.dual B)))
  let J := WeilDeligneRepresentation.inertiaKernelRepresentation I
    (WeilDeligneRepresentation.tensor
      (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.block ν A (n + 1)))
      (WeilDeligneRepresentation.dual (WeilDeligneRepresentation.block ν B (m + 1))))
  let J' := WeilDeligneRepresentation.inertiaKernelRepresentation I
    (WeilDeligneRepresentation.tensor
      (WeilDeligneRepresentation.block ν
        (FiniteRepresentation.twist χ (FiniteRepresentation.dual A)) (n + 1))
      (WeilDeligneRepresentation.block ν
        (FiniteRepresentation.twist ψ (FiniteRepresentation.dual B)) (m + 1)))
  let e := WeilDeligneRepresentation.tensorEquiv
    (WeilDeligneRepresentation.Blocks.blockDualEquiv ν A (n + 1))
    (WeilDeligneRepresentation.Blocks.blockDualEquiv ν B (m + 1))
  have hp := h K G ν I hν Φ
    (FiniteRepresentation.twist χ (FiniteRepresentation.dual A))
    (FiniteRepresentation.twist ψ (FiniteRepresentation.dual B)) n m
  change eulerPolynomial (J'.representation Φ) =
      (∏ j : Fin (min (n + 1) (m + 1)),
        eulerPolynomial ((ν Φ : K) ^ (n + m - j.val) • T.representation Φ)) ∧
    rationalFactor (J'.representation Φ) =
      (∏ j : Fin (min (n + 1) (m + 1)),
        rationalFactor ((ν Φ : K) ^ (n + m - j.val) • T.representation Φ)) ∧
    J'.rank = min (n + 1) (m + 1) * T.rank at hp
  have hpoly : eulerPolynomial (J.representation Φ) =
      ∏ j : Fin (min (n + 1) (m + 1)),
        eulerPolynomial ((ν Φ : K) ^ (-(j.val : ℤ)) • D.representation Φ) := by
    calc
      _ = eulerPolynomial (J'.representation Φ) :=
        WeilDeligne.eulerPolynomial_eq_of_equiv I e Φ
      _ = _ := hp.1
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        rw [eulerPolynomial_invariantsTensorTwist χ ψ I hχ hψ
          (FiniteRepresentation.dual A) (FiniteRepresentation.dual B) Φ]
        have hs : (ν Φ : K) ^ (n + m - j.val) * ((χ Φ : K) * (ψ Φ : K)) =
            (ν Φ : K) ^ (-(j.val : ℤ)) := by
          simpa only [χ, ψ, MonoidHom.zpow_apply] using dualPairTwist_scalar (ν Φ) n m j
        rw [hs]
  change eulerPolynomial (J.representation Φ) =
      (∏ j : Fin (min (n + 1) (m + 1)),
        eulerPolynomial ((ν Φ : K) ^ (-(j.val : ℤ)) • D.representation Φ)) ∧
    rationalFactor (J.representation Φ) =
      (∏ j : Fin (min (n + 1) (m + 1)),
        rationalFactor ((ν Φ : K) ^ (-(j.val : ℤ)) • D.representation Φ)) ∧
    J.rank = min (n + 1) (m + 1) * D.rank
  refine ⟨hpoly, ?_, ?_⟩
  · simp only [rationalFactor, hpoly, map_prod, Finset.prod_inv_distrib]
  · calc
      J.rank = J'.rank :=
        FiniteRepresentation.rank_eq_of_equiv (WeilDeligne.kernelEquiv I e)
      _ = min (n + 1) (m + 1) * T.rank := hp.2.2
      _ = min (n + 1) (m + 1) * D.rank := by
        rw [show T.rank = D.rank from
          (FiniteRepresentation.invariantsTensorTwistEquiv χ ψ I hχ hψ
            (FiniteRepresentation.dual A) (FiniteRepresentation.dual B)).finrank_eq.symm]

end Langlands.LocalFactor
