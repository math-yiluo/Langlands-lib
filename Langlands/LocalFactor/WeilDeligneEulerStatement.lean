import Langlands.LocalFactor.Euler
import Langlands.WeilDeligne.Dual
import Langlands.WeilDeligne.Kernels
import Langlands.WeilDeligne.SpecialBlocks
import Langlands.WeilDeligne.FrobeniusStatements

/-!
# Euler factors on actual Weil--Deligne monodromy kernels

These are algebraic theorem targets, using the genuine parameter constructions.
The normal subgroup and the norm character are explicit. Actual local Weil
specialization, epsilon factors and gamma factors are separate responsibilities.
-/

namespace Langlands.LocalFactor

open scoped BigOperators
open WeilDeligneRepresentation

universe uK uG uV uW

/-- Pair equivalences preserve the Euler polynomial and rational factor on
the inertia-fixed monodromy kernel. Representatives of the same inertia coset
give the same factor. Source and target carrier universes are independent. -/
def WDEulerInvarianceStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal] (Φ : G),
    (∀ (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
      (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν),
      Nonempty (WeilDeligneRepresentation.Equiv A B) →
      eulerPolynomial ((inertiaKernelRepresentation I A).representation Φ) =
        eulerPolynomial ((inertiaKernelRepresentation I B).representation Φ) ∧
      rationalFactor ((inertiaKernelRepresentation I A).representation Φ) =
        rationalFactor ((inertiaKernelRepresentation I B).representation Φ)) ∧
    (∀ (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) (Φ' : G),
      Φ' * Φ⁻¹ ∈ I →
      eulerPolynomial ((inertiaKernelRepresentation I A).representation Φ') =
        eulerPolynomial ((inertiaKernelRepresentation I A).representation Φ) ∧
      rationalFactor ((inertiaKernelRepresentation I A).representation Φ') =
        rationalFactor ((inertiaKernelRepresentation I A).representation Φ))

/-- Zero monodromy recovers the ordinary invariant-space factor. -/
def WDEulerZeroMonodromyStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal] (Φ : G)
    (A : FiniteRepresentation.{uK, uG, uV} K G),
    eulerPolynomial
        ((inertiaKernelRepresentation I (zeroMonodromy ν A)).representation Φ) =
      eulerPolynomial ((FiniteRepresentation.invariants I A).representation Φ) ∧
    rationalFactor
        ((inertiaKernelRepresentation I (zeroMonodromy ν A)).representation Φ) =
      rationalFactor ((FiniteRepresentation.invariants I A).representation Φ)

/-- Direct sums give products. This does not assert exactness of the
monodromy-kernel invariant functor on arbitrary short exact sequences. -/
def WDEulerDirectSumStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal] (Φ : G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν),
    eulerPolynomial
        ((inertiaKernelRepresentation I (WeilDeligneRepresentation.sum A B)).representation Φ) =
      eulerPolynomial ((inertiaKernelRepresentation I A).representation Φ) *
        eulerPolynomial ((inertiaKernelRepresentation I B).representation Φ) ∧
    rationalFactor
        ((inertiaKernelRepresentation I (WeilDeligneRepresentation.sum A B)).representation Φ) =
      rationalFactor ((inertiaKernelRepresentation I A).representation Φ) *
        rationalFactor ((inertiaKernelRepresentation I B).representation Φ)

/-- The kernel of an uncentered length `n+1` block has the top weight `ν^n`.
The norm must be trivial on the specified inertia subgroup. -/
def WDEulerBlockStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal],
    (∀ i : I, ν i = 1) →
    ∀ (Φ : G) (A : FiniteRepresentation.{uK, uG, uV} K G) (n : ℕ),
    let F := (FiniteRepresentation.invariants I A).representation Φ
    let J := inertiaKernelRepresentation I (block ν A (n + 1))
    eulerPolynomial (J.representation Φ) = eulerPolynomial ((ν Φ : K) ^ n • F) ∧
    rationalFactor (J.representation Φ) = rationalFactor ((ν Φ : K) ^ n • F) ∧
    J.rank = (FiniteRepresentation.invariants I A).rank

/-- The actual tensor product of two uncentered blocks has the pair-factor
exponents of Henniart 2002, §2.4. The characteristic-zero condition belongs
to the tensor Jordan-block calculation. Invariants are taken after tensoring
the Weil factors, not separately in the two factors. -/
def WDEulerPairBlockStatement : Prop :=
  ∀ (K : Type uK) [Field K] [CharZero K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal],
    (∀ i : I, ν i = 1) →
    ∀ (Φ : G)
      (A : FiniteRepresentation.{uK, uG, uV} K G)
      (B : FiniteRepresentation.{uK, uG, uW} K G) (n m : ℕ),
    let F := (FiniteRepresentation.invariants I
      (FiniteRepresentation.tensor A B)).representation Φ
    let J := inertiaKernelRepresentation I
      (WeilDeligneRepresentation.tensor (block ν A (n + 1)) (block ν B (m + 1)))
    eulerPolynomial (J.representation Φ) =
      ∏ j : Fin (min (n + 1) (m + 1)),
        eulerPolynomial ((ν Φ : K) ^ (n + m - j.val) • F) ∧
    rationalFactor (J.representation Φ) =
      ∏ j : Fin (min (n + 1) (m + 1)),
        rationalFactor ((ν Φ : K) ^ (n + m - j.val) • F) ∧
    J.rank = min (n + 1) (m + 1) *
      (FiniteRepresentation.invariants I (FiniteRepresentation.tensor A B)).rank

/-- The dual of an uncentered block has kernel weight zero, so its factor is
the factor of the dual Weil representation without an extra norm twist. -/
def WDEulerDualBlockStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal],
    (∀ i : I, ν i = 1) →
    ∀ (Φ : G) (A : FiniteRepresentation.{uK, uG, uV} K G) (n : ℕ),
    let F := (FiniteRepresentation.invariants I (FiniteRepresentation.dual A)).representation Φ
    let J := inertiaKernelRepresentation I (WeilDeligneRepresentation.dual (block ν A (n + 1)))
    eulerPolynomial (J.representation Φ) = eulerPolynomial F ∧
    rationalFactor (J.representation Φ) = rationalFactor F ∧
    J.rank = (FiniteRepresentation.invariants I (FiniteRepresentation.dual A)).rank

/-- The tensor of the two actual dual blocks has norm exponents `-j`,
not the exponents of the original blocks. Duals are formed before tensoring
and inertia invariants are taken after tensoring the dual Weil factors. -/
def WDEulerDualPairBlockStatement : Prop :=
  ∀ (K : Type uK) [Field K] [CharZero K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal],
    (∀ i : I, ν i = 1) →
    ∀ (Φ : G)
      (A : FiniteRepresentation.{uK, uG, uV} K G)
      (B : FiniteRepresentation.{uK, uG, uW} K G) (n m : ℕ),
    let D := FiniteRepresentation.invariants I
      (FiniteRepresentation.tensor (FiniteRepresentation.dual A) (FiniteRepresentation.dual B))
    let F := D.representation Φ
    let J := inertiaKernelRepresentation I
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.dual (block ν A (n + 1)))
        (WeilDeligneRepresentation.dual (block ν B (m + 1))))
    eulerPolynomial (J.representation Φ) =
      ∏ j : Fin (min (n + 1) (m + 1)),
        eulerPolynomial ((ν Φ : K) ^ (-(j.val : ℤ)) • F) ∧
    rationalFactor (J.representation Φ) =
      ∏ j : Fin (min (n + 1) (m + 1)),
        rationalFactor ((ν Φ : K) ^ (-(j.val : ℤ)) • F) ∧
    J.rank = min (n + 1) (m + 1) * D.rank

/-- An explicit commuting-unipotent change of the Frobenius operator leaves
the kernel factor unchanged. The supplied linear equivalence transports
monodromy and inertia; no semisimplification is chosen or postulated. -/
def WDEulerUnipotentChangeStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal] (Φ : G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν)
    (e : A ≃ₗ[K] B) (U : Module.End K A),
    IsNilpotent (U - 1) →
    Commute U A.monodromy →
    Commute U (A.representation Φ) →
    (∀ i : I, Commute U (A.representation i)) →
    e.toLinearMap.comp A.monodromy = B.monodromy.comp e.toLinearMap →
    (∀ i : I, e.toLinearMap.comp (A.representation i) =
      (B.representation i).comp e.toLinearMap) →
    B.representation Φ = e.conj (A.representation Φ * U) →
    eulerPolynomial ((inertiaKernelRepresentation I B).representation Φ) =
      eulerPolynomial ((inertiaKernelRepresentation I A).representation Φ) ∧
    rationalFactor ((inertiaKernelRepresentation I B).representation Φ) =
      rationalFactor ((inertiaKernelRepresentation I A).representation Φ)

/-- Frobenius semisimplification preserves the actual invariant-kernel Euler
polynomial and rational factor. The relation supplies the corrected action
and transported monodromy; no existence theorem or chosen output is assumed.
The degree-one element is the geometric Frobenius convention. -/
def WDEulerSemisimplificationStatement : Prop :=
  ∀ (G : Type uG) [Group G] (ν : G →* ℂˣ)
    (degree : G →* Multiplicative ℤ) (Φ : G),
    Multiplicative.toAdd (degree Φ) = 1 →
    ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
      Frobenius.IsSemisimplification degree A B →
      eulerPolynomial ((inertiaKernelRepresentation degree.ker B).representation Φ) =
        eulerPolynomial ((inertiaKernelRepresentation degree.ker A).representation Φ) ∧
      rationalFactor ((inertiaKernelRepresentation degree.ker B).representation Φ) =
        rationalFactor ((inertiaKernelRepresentation degree.ker A).representation Φ)

/-- The algebraic Euler-factor family on actual inertia-fixed monodromy kernels.
It supplies the kernel/block part of the arithmetic target, not local epsilon
existence, an actual local Weil group, or the LLC. -/
def WeilDeligneEulerStatement : Prop :=
  WDEulerInvarianceStatement.{uK, uG, uV, uW} ∧
  WDEulerZeroMonodromyStatement.{uK, uG, uV} ∧
  WDEulerDirectSumStatement.{uK, uG, uV, uW} ∧
  WDEulerBlockStatement.{uK, uG, uV} ∧
  WDEulerPairBlockStatement.{uK, uG, uV, uW} ∧
  WDEulerDualBlockStatement.{uK, uG, uV} ∧
  WDEulerDualPairBlockStatement.{uK, uG, uV, uW} ∧
  WDEulerUnipotentChangeStatement.{uK, uG, uV, uW} ∧
  WDEulerSemisimplificationStatement.{uG, uV, uW}

end Langlands.LocalFactor
