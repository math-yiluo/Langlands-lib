import Langlands.Representation.Archimedean.RealLinkedJacquetFunctional
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-!
# The linked Jacquet functional statement: lists of characters and lists with an induction block

`RealLinkedJacquetFunctionalStatement` (S2) asks, for a Langlands-ordered list `ds` of real
blocks of total rank `n` with two linked Mœglin data, for a nonzero real Jacquet functional `ℓ`
on the `O(n)`-finite functions of the standard module of `ds`, with exponents `a`, signs `e`, a
position `p` with `p + 1 < n` and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and
`ℓ ∘ π(E_{p+1,p})^k = 0`.

This file splits S2 according to the kinds of blocks of `ds`:

* `RealCharacterLinkedJacquetFunctionalStatement`: S2 for lists all of whose blocks are real
  characters (`RealStrictCharacterLanglandsQuotient.IsCharacterList ds`);
* `RealInducedLinkedJacquetFunctionalStatement`: S2 for lists with at least one block that is
  not a real character, that is, an induction block `RealBlock.induced`.

`realLinkedJacquetFunctional_of_cases` proves S2 from the two statements.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open RealStrictCharacterLanglandsQuotient (IsCharacterList)

/-- **S2 for lists of real characters.** For a list `ds` of real characters (`IsCharacterList`)
of total rank `n` in Langlands order, two of whose Mœglin data are linked, there are a nonzero
real Jacquet functional `ℓ` on the `O(n)`-finite functions of the standard module of `ds`, with
exponents `a` and signs `e`, a position `p` with `p + 1 < n` and `k : ℕ` such that
`a_p - a_{p+1} = 1 - k` and `ℓ(π(E_{p+1,p})^k v) = 0` for every `v`. -/
def RealCharacterLinkedJacquetFunctionalStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsCharacterList ds →
    IsRealLanglandsOrdered ds → ¬ IsRealMoeglinUnlinked ds →
      ∃ (ℓ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ)
        (a : Fin n → ℂ) (e : Fin n → Fin 2) (p k : ℕ) (hp : p + 1 < n),
        ℓ ≠ 0 ∧ IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
          ℓ a e ∧
          a ⟨p, Nat.lt_of_succ_lt hp⟩ - a ⟨p + 1, hp⟩ = 1 - (k : ℂ) ∧
          ∀ v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
            ℓ ((realStandardLie n ds (1 ⊗ₜ lowerRootMatrix n p hp) ^ k) v) = 0

/-- **S2 for lists with an induction block.** For a list `ds` of real blocks of total rank `n`
in Langlands order that is not a list of real characters (`¬ IsCharacterList ds`), two of whose
Mœglin data are linked, there are a nonzero real Jacquet functional `ℓ` on the `O(n)`-finite
functions of the standard module of `ds`, with exponents `a` and signs `e`, a position `p` with
`p + 1 < n` and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and `ℓ(π(E_{p+1,p})^k v) = 0` for
every `v`. -/
def RealInducedLinkedJacquetFunctionalStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → ¬ IsCharacterList ds →
    IsRealLanglandsOrdered ds → ¬ IsRealMoeglinUnlinked ds →
      ∃ (ℓ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ)
        (a : Fin n → ℂ) (e : Fin n → Fin 2) (p k : ℕ) (hp : p + 1 < n),
        ℓ ≠ 0 ∧ IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
          ℓ a e ∧
          a ⟨p, Nat.lt_of_succ_lt hp⟩ - a ⟨p + 1, hp⟩ = 1 - (k : ℂ) ∧
          ∀ v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
            ℓ ((realStandardLie n ds (1 ⊗ₜ lowerRootMatrix n p hp) ^ k) v) = 0

/-- The two cases give `RealLinkedJacquetFunctionalStatement`. -/
theorem realLinkedJacquetFunctional_of_cases
    (hC : RealCharacterLinkedJacquetFunctionalStatement)
    (hI : RealInducedLinkedJacquetFunctionalStatement) :
    RealLinkedJacquetFunctionalStatement := by
  intro n ds hrank hord hlink
  by_cases hc : IsCharacterList ds
  · exact hC n ds hrank hc hord hlink
  · exact hI n ds hrank hc hord hlink

end Langlands.Archimedean
