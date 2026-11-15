import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleReduction

/-!
# Splitting Vogan's irreducibility statement for `GL_n(ℂ)` along the linkage criterion

`ComplexLargeStandardIrreducibleStatement` says that a Langlands-ordered complex standard module
whose Langlands quotient is maximally faithful is irreducible. This file splits it along the
irreducibility criterion for principal series of `GL_n(ℂ)` (Tadić 2009, §3, p. 11 and
Lemmas 3.2–3.3, pp. 12–13):

* `ComplexStandardIrreducibleCriterionStatement` (the "if" part of the criterion): if no two
  of the characters are linked, the standard module is irreducible;
* `ComplexLinkedLanglandsQuotientNotLargeStatement`: if two of the characters are linked, the
  Langlands quotient is not maximally faithful.

`complexLargeStandardIrreducibleSplit` proves that the two imply
`ComplexLargeStandardIrreducibleStatement`.

Tadić's parameters: the character `z ↦ (z/|z|)^l |z|^(2t)` of `ℂˣ` is `γ(x, y)` with
`x = t + l/2` and `y = t - l/2`, where `γ(x, y)(z) = |z|^(x+y) (z/|z|)^(x-y)`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `ComplexLargeStandardIrreducibleReduction`: the charts on units need reduction through
-- the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

/-! ## Linked characters -/

/-- Two complex characters are linked (Tadić 2009, p. 11) when, writing them as
`γ(x₁, y₁)` and `γ(x₂, y₂)` with `x = t + l/2` and `y = t - l/2` for the character
`z ↦ (z/|z|)^l |z|^(2t)`, the differences `p = x₁ - x₂` and `q = y₁ - y₂` are integers with
`p q > 0`. Equivalently, the quotient of the two characters is `z ↦ z^p z̄^q` with `p q > 0`.
The relation is symmetric. -/
def IsComplexLinked (d e : ComplexCharacterData) : Prop :=
  ∃ p q : ℤ, 0 < p * q ∧
    (d.exponent + (d.weight : ℂ) / 2) - (e.exponent + (e.weight : ℂ) / 2) = p ∧
    (d.exponent - (d.weight : ℂ) / 2) - (e.exponent - (e.weight : ℂ) / 2) = q

/-- No two characters of the list `ds` are linked: the condition of Tadić 2009 (p. 11 and
Lemmas 3.2–3.3) for the principal series of `ds` to be irreducible. -/
def IsComplexUnlinked (ds : List ComplexCharacterData) : Prop :=
  ds.Pairwise fun d e => ¬ IsComplexLinked d e

/-! ## The two statements and the reduction -/

/-- The irreducibility criterion for principal series of `GL_n(ℂ)`, "if" part (Tadić 2009,
p. 11 and Lemmas 3.2–3.3): for a list `ds` of `n` complex characters in Langlands order, if no
two of them are linked, the `(𝔤𝔩_n(ℂ), U(n))`-module of `U(n)`-finite functions of the standard
module of `ds` is irreducible. -/
def ComplexStandardIrreducibleCriterionStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n → IsComplexLanglandsOrdered ds →
    IsComplexUnlinked ds →
      IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)

/-- The Langlands quotient of a complex standard module with a linked pair is not large: for a
list `ds` of `n` complex characters in Langlands order, two of which are linked, and the
largest proper `(𝔤, K)`-submodule `R` of the `U(n)`-finite functions of its standard module,
the Langlands quotient by `R` is not maximally faithful. -/
def ComplexLinkedLanglandsQuotientNotLargeStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData)
    (R : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))),
    ds.length = n → IsComplexLanglandsOrdered ds → ¬ IsComplexUnlinked ds →
      IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) R → R ≠ ⊤ →
        (∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
          IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W → W ≠ ⊤ → W ≤ R) →
          ¬ IsMaximallyFaithfulModulo (complexStandardLie n ds) R

/-- The irreducibility criterion and the non-largeness of Langlands quotients with a linked
pair imply Vogan's irreducibility statement `ComplexLargeStandardIrreducibleStatement`. -/
def ComplexLargeStandardIrreducibleSplitStatement : Prop :=
  ComplexStandardIrreducibleCriterionStatement →
    ComplexLinkedLanglandsQuotientNotLargeStatement → ComplexLargeStandardIrreducibleStatement

/-- The reduction: with a linked pair the hypothesis of maximal faithfulness contradicts
`ComplexLinkedLanglandsQuotientNotLargeStatement`; without one the standard module is
irreducible, so its proper `(𝔤, K)`-submodule `R` is `⊥`. -/
theorem complexLargeStandardIrreducibleSplit : ComplexLargeStandardIrreducibleSplitStatement := by
  intro hSp hNL n ds R hlen hord hRgk hRtop hRmax hmf
  by_cases hu : IsComplexUnlinked ds
  · rcases (hSp n ds hlen hord hu).2 R hRgk.1 hRgk.2 with h | h
    · exact h
    · exact absurd h hRtop
  · exact absurd hmf (hNL n ds R hlen hord hu hRgk hRtop hRmax)

end Langlands.Archimedean
