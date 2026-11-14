/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 489, 14 November 2026: extract the signatures of the six
source-private theorems M351.005–M351.010 (source lines 196–397) from
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued
targets Langlands.NYLL.PortInternal.M351.d005Statement–d010Statement.
Each target takes the source binders, including hypotheses, as parameters in
source order and kinds, and has the source conclusion as its body; it is
reducible (abbrev). Hypothesis parameters, unused in the bodies, carry an
underscore prefix. The source's `Type*` universes for R, τ and ι are named
u, v and w, independently. The unused source section variables (K, F, π, σ
and [Fintype σ]), the local instance Classical.propDecidable and the import
of RecursiveCoefficient are not used by these signatures and are dropped;
the import is Mathlib.RingTheory.MvPowerSeries.Order only. Source proofs are
omitted. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Targets for order estimates of multivariable power series

Proposition targets for the source-private order estimates M351.005–M351.010
of `Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`: lower
bounds for the order of a monomial, of a power, of a finite sum, of a finite
product of powers, of a difference of two powers and of a difference of two
finite products of powers. See the paired Markdown.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

/-- Target of M351.005 (private `degree_le_order_monomial_stabilization`):
the order of the monomial `c X^d` is at least the total degree of `d`. -/
abbrev d005Statement
    {R : Type u} [CommRing R] {τ : Type v}
    (d : τ →₀ ℕ) (c : R) : Prop :=
  (d.degree : ℕ∞) ≤ (MvPowerSeries.monomial d c).order

/-- Target of M351.006 (private
`natCast_le_order_pow_of_one_le_order_stabilization`): if `f` has order at
least one, then `f ^ n` has order at least `n`. -/
abbrev d006Statement
    {R : Type u} [CommRing R] {τ : Type v}
    (f : MvPowerSeries τ R) (n : ℕ)
    (_hf : (1 : ℕ∞) ≤ f.order) : Prop :=
  (n : ℕ∞) ≤ (f ^ n).order

/-- Target of M351.007 (private `le_order_finset_sum_stabilization`): a
common lower bound for the orders of the summands bounds the order of a
finite sum. -/
abbrev d007Statement
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι} {f : ι → MvPowerSeries τ R} {m : ℕ∞}
    (_h : ∀ i ∈ s, m ≤ (f i).order) : Prop :=
  m ≤ (∑ i ∈ s, f i).order

/-- Target of M351.008 (private
`natCast_sum_le_order_finset_prod_pow_stabilization`): if every factor has
order at least one, then `∏ i ∈ s, f i ^ n i` has order at least
`∑ i ∈ s, n i`. -/
abbrev d008Statement
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι} (f : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (_hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order) : Prop :=
  ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤
    (∏ i ∈ s, (f i) ^ n i).order

/-- Target of M351.009 (private
`order_sub_add_pred_le_order_pow_sub_pow_stabilization`): for `f` and `g` of
order at least one, `f ^ n - g ^ n` has order at least
`(f - g).order + (n - 1)`, with truncated natural subtraction `n - 1`. -/
abbrev d009Statement
    {R : Type u} [CommRing R] {τ : Type v}
    (f g : MvPowerSeries τ R)
    (_hf : (1 : ℕ∞) ≤ f.order)
    (_hg : (1 : ℕ∞) ≤ g.order)
    (n : ℕ) : Prop :=
  (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
    (f ^ n - g ^ n).order

/-- Target of M351.010 (private
`natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization`): if every
exponent on `s` is nonzero, all `f i` and `g i` have order at least one and
every `f i - g i` has order at least two, then the difference of the two
finite products of powers has order at least `∑ i ∈ s, n i + 1`. -/
abbrev d010Statement
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι}
    (f g : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (_hn : ∀ i ∈ s, n i ≠ 0)
    (_hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order)
    (_hg : ∀ i ∈ s, (1 : ℕ∞) ≤ (g i).order)
    (_hfg : ∀ i ∈ s, (2 : ℕ∞) ≤ (f i - g i).order) : Prop :=
  (((∑ i ∈ s, n i) + 1 : ℕ) : ℕ∞) ≤
    ((∏ i ∈ s, (f i) ^ n i) -
      ∏ i ∈ s, (g i) ^ n i).order

end Langlands.NYLL.PortInternal.M351
