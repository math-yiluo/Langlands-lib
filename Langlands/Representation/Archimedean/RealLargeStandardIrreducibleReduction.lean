import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-!
# Splitting Vogan's irreducibility statement for `GL_n(ℝ)` along Speh's criterion

`RealLargeStandardIrreducibleStatement` says that a Langlands-ordered real standard module
whose Langlands quotient is maximally faithful is irreducible. This file splits it along
Speh's irreducibility criterion for standard modules of `GL_n(ℝ)` (Mœglin 1997,
Theorem 10b, after Speh's thesis):

* `RealStandardIrreducibleCriterionStatement` (the "if" part of Speh's criterion): if no two
  of the Mœglin data of the blocks are linked, the standard module is irreducible;
* `RealLinkedLanglandsQuotientNotLargeStatement`: if two of the Mœglin data of the blocks
  are linked, the Langlands quotient is not maximally faithful.

`realLargeStandardIrreducibleReduction` proves that the two imply
`RealLargeStandardIrreducibleStatement`.

Mœglin's data: each one-dimensional block `sgn^ε |·|^s` gives the datum `(1, s, sgn^ε)`, and
each discrete-series block `D_p ⊗ |det|^s` of `GL_2(ℝ)` (`D_p` the discrete series with
infinitesimal character `(p/2, -p/2)`, `p ≥ 1`) gives the datum `(2, s, D_p)`. A Library
block `RealBlock.induced d` of weight `m ≠ 0` is `D_|m| ⊗ |det|^t`; one of weight `0` is the
full principal series `sgn |·|^t × |·|^t` and gives the two data `(1, t, sgn)`, `(1, t, 1)`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `RealGenericLargeReduction`: the charts on units need reduction through the
-- normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

/-! ## Mœglin's data and linked pairs -/

/-- A datum `(n_j, s_j, σ_j)` of Mœglin (1997, §10, p. 164) with `n_j ∈ {1, 2}`:
`character ε s` is `(1, s, sgn^ε)`, the character `sgn^ε |·|^s` of `GL_1(ℝ)`, and
`discrete p s` is `(2, s, σ)` with `σ` the discrete series of `GL_2(ℝ)` with infinitesimal
character `(p/2, -p/2)`, twisted by `|det|^s`. Mœglin requires `p ≥ 1`; the data produced
from real blocks by `realBlockMoeglinData` satisfy this. -/
inductive MoeglinDatum where
  | character (parity : Fin 2) (exponent : ℂ)
  | discrete (p : ℕ) (exponent : ℂ)

/-- Two Mœglin data are linked when they violate the condition of Mœglin 1997,
Theorem 10b, for the pair:

* two characters `sgn^ε |·|^s`, `sgn^ε' |·|^s'` are linked when `s - s'` is a nonzero
  integer, odd if `ε = ε'` and even if `ε ≠ ε'` (condition (i));
* a discrete series datum `(2, s, D_p)` and a character datum `(1, s', σ')` are linked when
  `s - s'` is real and `|s - s'| - p/2 ∈ {1, 2, 3, …}` (condition (ii));
* two discrete series data `(2, s, D_p)`, `(2, s', D_p')` are linked when `s - s'` is real
  and `|s - s'| - |p - p'|/2 ∈ {1, 2, 3, …}` (condition (iii)).

The relation is symmetric. -/
def MoeglinDatum.IsLinked : MoeglinDatum → MoeglinDatum → Prop
  | .character ε s, .character ε' s' =>
      ∃ k : ℤ, k ≠ 0 ∧ s - s' = k ∧ Odd (k + (ε.val : ℤ) + (ε'.val : ℤ))
  | .discrete p s, .character _ s' =>
      ∃ k : ℕ, 0 < k ∧ (s - s' = (p : ℂ) / 2 + k ∨ s' - s = (p : ℂ) / 2 + k)
  | .character _ s, .discrete p s' =>
      ∃ k : ℕ, 0 < k ∧ (s' - s = (p : ℂ) / 2 + k ∨ s - s' = (p : ℂ) / 2 + k)
  | .discrete p s, .discrete p' s' =>
      ∃ k : ℕ, 0 < k ∧
        (s - s' = (((p : ℤ) - p').natAbs : ℂ) / 2 + k ∨
          s' - s = (((p : ℤ) - p').natAbs : ℂ) / 2 + k)

/-- The Mœglin data of a real block. A character block `sgn^ε |·|^t` gives `(1, t, sgn^ε)`.
The real induction of `(z/|z|)^m |z|^(2t)` with `m ≠ 0` is the subrepresentation
`D_|m| ⊗ |det|^t` (infinitesimal character `(t + |m|/2, t - |m|/2)`) of the principal series
`sgn^(|m|+1) |·|^(t+|m|/2) × |·|^(t-|m|/2)` and gives `(2, t, D_|m|)`. For `m = 0` the
Library's block is the whole principal series `sgn |·|^t × |·|^t`, which gives the two data
`(1, t, sgn)` and `(1, t, 1)`. -/
def realBlockMoeglinData : RealBlock → List MoeglinDatum
  | .character d => [.character d.parity d.exponent]
  | .induced d =>
      if d.weight = 0 then [.character 1 d.exponent, .character 0 d.exponent]
      else [.discrete d.weight.natAbs d.exponent]

/-- The Mœglin data of a list of real blocks, in order. -/
def realMoeglinData (ds : List RealBlock) : List MoeglinDatum :=
  ds.flatMap realBlockMoeglinData

/-- No two Mœglin data of the blocks `ds` are linked: the condition of Mœglin 1997,
Theorem 10b, for the standard module of `ds` to be irreducible. -/
def IsRealMoeglinUnlinked (ds : List RealBlock) : Prop :=
  (realMoeglinData ds).Pairwise fun a b => ¬ a.IsLinked b

/-! ## The two statements and the reduction -/

/-- Speh's irreducibility criterion, "if" part (Mœglin 1997, Theorem 10b, citing Speh's
thesis): for a list `ds` of real blocks of total rank `n` in Langlands order, if no two
Mœglin data of the blocks are linked, the `(𝔤𝔩_n(ℝ), O(n))`-module of `O(n)`-finite
functions of the standard module of `ds` is irreducible. -/
def RealStandardIrreducibleCriterionStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsRealLanglandsOrdered ds →
    IsRealMoeglinUnlinked ds →
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)

/-- The Langlands quotient of a standard module with a linked pair is not large: for a list
`ds` of real blocks of total rank `n` in Langlands order, two of whose Mœglin data are
linked, and the largest proper `(𝔤, K)`-submodule `R` of the `O(n)`-finite functions of its
standard module, the Langlands quotient by `R` is not maximally faithful. -/
def RealLinkedLanglandsQuotientNotLargeStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock)
    (R : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))),
    realRank ds = n → IsRealLanglandsOrdered ds → ¬ IsRealMoeglinUnlinked ds →
      IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) R → R ≠ ⊤ →
        (∀ W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
          IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W → W ≠ ⊤ → W ≤ R) →
          ¬ IsMaximallyFaithfulModulo (realStandardLie n ds) R

/-- Speh's criterion and the non-largeness of Langlands quotients with a linked pair imply
Vogan's irreducibility statement `RealLargeStandardIrreducibleStatement`. -/
def RealLargeStandardIrreducibleReductionStatement : Prop :=
  RealStandardIrreducibleCriterionStatement → RealLinkedLanglandsQuotientNotLargeStatement →
    RealLargeStandardIrreducibleStatement

/-- The reduction: with a linked pair the hypothesis of maximal faithfulness contradicts
`RealLinkedLanglandsQuotientNotLargeStatement`; without one the standard module is
irreducible, so its proper `(𝔤, K)`-submodule `R` is `⊥`. -/
theorem realLargeStandardIrreducibleReduction :
    RealLargeStandardIrreducibleReductionStatement := by
  intro hSp hNL n ds R hrank hord hRgk hRtop hRmax hmf
  by_cases hu : IsRealMoeglinUnlinked ds
  · rcases (hSp n ds hrank hord hu).2 R hRgk.1 hRgk.2 with h | h
    · exact h
    · exact absurd h hRtop
  · exact absurd hmf (hNL n ds R hrank hord hu hRgk hRtop hRmax)

end Langlands.Archimedean
