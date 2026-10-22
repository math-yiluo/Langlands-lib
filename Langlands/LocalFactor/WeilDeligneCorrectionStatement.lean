import Langlands.LocalFactor.WeilDeligne
import Langlands.WeilDeligne.SpecialBlocks
import Langlands.WeilDeligne.FrobeniusStatements

/-!
# Structural laws for the actual Weil--Deligne quotient correction

These proposition definitions use the constructed representation on
`V^I / (ker N)^I`. They do not assume a nonabelian epsilon system or assert
multiplicativity for arbitrary short exact sequences of Weil--Deligne pairs.
-/

namespace Langlands.LocalFactor

open scoped BigOperators
open WeilDeligneRepresentation

universe uK uG uV uW

/-- The actual kernel-invariant subspace and quotient give determinant
factorization inside the fixed space of one pair. This is not an exactness
claim about applying fixed monodromy kernels to an arbitrary sequence. -/
def WDCorrectionSubquotientStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal] (Φ : G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν),
    eulerPolynomial (WeilDeligne.inertiaOperator A I Φ) =
      eulerPolynomial (WeilDeligne.kernelOperator A I Φ) *
        eulerPolynomial (WeilDeligne.quotientOperator A I Φ) ∧
    rationalFactor (WeilDeligne.inertiaOperator A I Φ) =
      WeilDeligne.rationalLFactor A I Φ *
        rationalFactor (WeilDeligne.quotientOperator A I Φ) ∧
    LinearMap.det (-WeilDeligne.inertiaOperator A I Φ) =
      LinearMap.det (-WeilDeligne.kernelOperator A I Φ) *
        WeilDeligne.quotientDeterminant A I Φ

/-- Actual direct sums give sums of correction dimensions and products of
constant, polynomial and rational corrections. -/
def WDCorrectionDirectSumStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal] (Φ : G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν),
    WeilDeligne.conductorCorrection (WeilDeligneRepresentation.sum A B) I =
      WeilDeligne.conductorCorrection A I + WeilDeligne.conductorCorrection B I ∧
    WeilDeligne.quotientDeterminant (WeilDeligneRepresentation.sum A B) I Φ =
      WeilDeligne.quotientDeterminant A I Φ * WeilDeligne.quotientDeterminant B I Φ ∧
    WeilDeligne.quotientCorrectionPolynomial (WeilDeligneRepresentation.sum A B) I Φ =
      WeilDeligne.quotientCorrectionPolynomial A I Φ *
        WeilDeligne.quotientCorrectionPolynomial B I Φ ∧
    WeilDeligne.quotientCorrection (WeilDeligneRepresentation.sum A B) I Φ =
      WeilDeligne.quotientCorrection A I Φ * WeilDeligne.quotientCorrection B I Φ

/-- A length `n+1` uncentered block has quotient weights `0,...,n-1`.
The last weight is its monodromy kernel and is excluded from the correction. -/
def WDCorrectionBlockStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal],
    (∀ i : I, ν i = 1) →
    ∀ (Φ : G) (A : FiniteRepresentation.{uK, uG, uV} K G) (n : ℕ),
    let D := FiniteRepresentation.invariants I A
    let F := D.representation Φ
    let B := block ν A (n + 1)
    let P := ∏ i : Fin n,
      Polynomial.monomial D.rank (LinearMap.det (-((ν Φ : K) ^ i.val • F)))
    WeilDeligne.conductorCorrection B I = n * D.rank ∧
    WeilDeligne.quotientDeterminant B I Φ =
      ∏ i : Fin n, LinearMap.det (-((ν Φ : K) ^ i.val • F)) ∧
    WeilDeligne.quotientCorrectionPolynomial B I Φ = P ∧
    WeilDeligne.quotientCorrection B I Φ = algebraMap (Polynomial K) (RatFunc K) P

/-- The quotient correction for a pair of blocks is the determinant on all
tensor weights divided by the determinant on the actual monodromy kernel.
Tensor-kernel weights require characteristic zero. -/
def WDCorrectionPairBlockStatement : Prop :=
  ∀ (K : Type uK) [Field K] [CharZero K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal],
    (∀ i : I, ν i = 1) →
    ∀ (Φ : G)
      (A : FiniteRepresentation.{uK, uG, uV} K G)
      (B : FiniteRepresentation.{uK, uG, uW} K G) (n m : ℕ),
    let D := FiniteRepresentation.invariants I (FiniteRepresentation.tensor A B)
    let F := D.representation Φ
    let T := WeilDeligneRepresentation.tensor (block ν A (n + 1)) (block ν B (m + 1))
    let P := ∏ i : Fin (n + 1), ∏ j : Fin (m + 1),
      Polynomial.monomial D.rank
        (LinearMap.det (-((ν Φ : K) ^ (i.val + j.val) • F)))
    let Q := ∏ j : Fin (min (n + 1) (m + 1)),
      Polynomial.monomial D.rank
        (LinearMap.det (-((ν Φ : K) ^ (n + m - j.val) • F)))
    WeilDeligne.conductorCorrection T I =
      ((n + 1) * (m + 1) - min (n + 1) (m + 1)) * D.rank ∧
    Q ≠ 0 ∧
    WeilDeligne.quotientCorrectionPolynomial T I Φ * Q = P ∧
    WeilDeligne.quotientCorrection T I Φ =
      algebraMap (Polynomial K) (RatFunc K) P /
        algebraMap (Polynomial K) (RatFunc K) Q

/-- A specified commuting-unipotent change preserves the quotient dimension
and determinant, hence both corrections. The actual equivalence transports
monodromy and the entire inertia action. -/
def WDCorrectionUnipotentChangeStatement : Prop :=
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
    WeilDeligne.conductorCorrection B I = WeilDeligne.conductorCorrection A I ∧
    WeilDeligne.quotientDeterminant B I Φ = WeilDeligne.quotientDeterminant A I Φ ∧
    WeilDeligne.quotientCorrectionPolynomial B I Φ =
      WeilDeligne.quotientCorrectionPolynomial A I Φ ∧
    WeilDeligne.quotientCorrection B I Φ = WeilDeligne.quotientCorrection A I Φ

/-- The actual Frobenius-semisimplification relation preserves the monodromy
correction. Its existence and its desired factor identity are not hypotheses. -/
def WDCorrectionSemisimplificationStatement : Prop :=
  ∀ (G : Type uG) [Group G] (ν : G →* ℂˣ)
    (degree : G →* Multiplicative ℤ) (Φ : G),
    Multiplicative.toAdd (degree Φ) = 1 →
    ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
      Frobenius.IsSemisimplification degree A B →
      WeilDeligne.conductorCorrection B degree.ker =
        WeilDeligne.conductorCorrection A degree.ker ∧
      WeilDeligne.quotientDeterminant B degree.ker Φ =
        WeilDeligne.quotientDeterminant A degree.ker Φ ∧
      WeilDeligne.quotientCorrectionPolynomial B degree.ker Φ =
        WeilDeligne.quotientCorrectionPolynomial A degree.ker Φ ∧
      WeilDeligne.quotientCorrection B degree.ker Φ =
        WeilDeligne.quotientCorrection A degree.ker Φ

/-- Vanishing of the actual inertia-fixed space removes both L and the
monodromy correction. A ramification theorem proving this premise for a
twist is separate; it is not silently assumed for every representation. -/
def WDCorrectionNoInvariantsStatement : Prop :=
  ∀ (K : Type uK) [Field K] (G : Type uG) [Group G]
    (ν : G →* Kˣ) (I : Subgroup G) [I.Normal] (Φ : G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν),
    (WeilDeligne.inertiaRepresentation A I).rank = 0 →
    WeilDeligne.conductorCorrection A I = 0 ∧
    WeilDeligne.eulerPolynomial A I Φ = 1 ∧
    WeilDeligne.rationalLFactor A I Φ = 1 ∧
    WeilDeligne.quotientDeterminant A I Φ = 1 ∧
    WeilDeligne.quotientCorrectionPolynomial A I Φ = 1 ∧
    WeilDeligne.quotientCorrection A I Φ = 1

/-- The structural family for the constructed quotient determinant. It
supplies no epsilon system, Artin conductor or arbitrary WD exactness law. -/
def WeilDeligneCorrectionStatement : Prop :=
  WDCorrectionSubquotientStatement.{uK, uG, uV} ∧
  WDCorrectionDirectSumStatement.{uK, uG, uV, uW} ∧
  WDCorrectionBlockStatement.{uK, uG, uV} ∧
  WDCorrectionPairBlockStatement.{uK, uG, uV, uW} ∧
  WDCorrectionUnipotentChangeStatement.{uK, uG, uV, uW} ∧
  WDCorrectionSemisimplificationStatement.{uG, uV, uW} ∧
  WDCorrectionNoInvariantsStatement.{uK, uG, uV}

end Langlands.LocalFactor
