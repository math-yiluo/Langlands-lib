# The Whittaker expansion of the dual cusp forms

The module defines the predicate
`Langlands.Global.RankinSelbergGlobal.Unfolding.DualCuspidalWhittakerExpansion`
and the Prop-valued statement
`Langlands.Global.RankinSelbergGlobal.DualCuspidalWhittakerExpansionStatement.{u}`.
No proof is supplied.

Provenance: derived. It is Cogdell's Theorem 1.1 (Whittaker expansion, with
absolute convergence uniform on compact sets) applied to the dual cusp form
`φ̃` and the character `ψ⁻¹`, written with the Library's dual functions.

## The predicate

Let `F` be a number field with `CompactSpace (AdeleQuotient F)`, let
`T : Automorphic.CuspidalOperatorRealization F r` be an actual cuspidal
realization of rank `n = r + 1`, and write, for a standard additive
character `ψ` (`IsStandardAdditiveCharacter F ψ`) and a vector `v`,

- `φ = cuspFunction F T v`, the cusp form of `v`;
- `W = cuspWhittaker F T ψ v`, its `ψ`-Whittaker function;
- `φ̃ = dualFunction F (r + 1) φ` and `W̃ = dualFunction F (r + 1) W`, where
  `dualFunction F n f (g) = f(w_n ᵗg⁻¹)` (published module `UnequalIntegrals`).

`DualCuspidalWhittakerExpansion F T` states: for every standard `ψ` and
every vector `v`,

1. for every `g ∈ GL_n(𝔸)` (`g : Points F (r + 1)`), the family
   `q ↦ W̃(diag(q.out, 1) g)` over `q : UnipotentRationalCosets F r`
   (the cosets `N_r(F) \ GL_r(F)`, with `diag(q.out, 1)` given by
   `cornerAdelicPoint F r q.out`) is absolutely summable (`Summable` of the
   norms) and has sum `φ̃(g)` (`HasSum`);
2. for every compact set `C ⊆ GL_n(𝔸)`, the finite partial sums
   `g ↦ ∑_{q ∈ s} ‖W̃(diag(q.out, 1) g)‖` converge to the full sum
   `g ↦ ∑' q, ‖W̃(diag(q.out, 1) g)‖` uniformly on `C` along the filter
   `atTop` of finite sets `s` (`TendstoUniformlyOn`).

`DualCuspidalWhittakerExpansionStatement` asserts the predicate for every
number field `F : Type u` with compact `AdeleQuotient F`, every `r` and
every actual cuspidal realization `T` of rank `r + 1`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), source
`cogdell-2004-analytic-theory-gln`.

- Theorem 1.1, printed p.200 (PDF p.203): for a cusp form `φ` on `GL_n(𝔸)`
  with `ψ`-Whittaker function `W_φ`,
  `φ(g) = Σ_{γ ∈ N_{n-1}(k) \ GL_{n-1}(k)} W_φ(diag(γ, 1) g)`
  "with convergence absolute and uniform on compact subsets".
- Printed p.206 (PDF p.209): the dual form is `φ̃(g) = φ(w_n ᵗg⁻¹)`, a cusp
  form in the contragredient `π̃`. Printed p.207 (PDF p.210): "for
  `W ∈ W(π, ψ)`, we set `W̃(g) = W(w_n ᵗg⁻¹) ∈ W(π̃, ψ⁻¹)`."

Applying Theorem 1.1 to `φ̃` and the character `ψ⁻¹` gives clause 1, once
`W̃` is identified with the `ψ⁻¹`-Whittaker function of `φ̃`. The
identification is the change of variables `n ↦ w_n ᵗn⁻¹ w_n⁻¹` on
`N_n(F) \ N_n(𝔸)`. This map preserves the quotient measure and inverts the
generic character (published lemmas `measurePreserving_dualConjUnipotent`
and `genericCharacter_dualConjUnipotent`, module `UnfoldingDualGL`).
Clause 2 is the uniformity on compact sets in Theorem 1.1, in the form used
by the Library (uniform convergence of the sums of absolute values).

## Role

Task 6838 needs this expansion, including the locally uniform clause, to
prove the dual expansion E' (`DualProjectionWhittakerExpansion`, published
module `UnfoldingDual`) for every actual unequal-rank pair. The proof
integrates the expansion of `φ̃` termwise over a compact unipotent quotient
and dominates the terms by the locally bounded function
`g ↦ ∑' q, ‖W̃(diag(q.out, 1) g)‖`. Pointwise absolute summability alone
does not give this bound. The statement parallels the published
`CuspidalWhittakerExpansionStatement` (module
`ProjectionExpansionReduction`) for `φ`. A proof may start from the
Library's `Langlands.Global.WhittakerExpansionStatement` applied to `φ̃`.
