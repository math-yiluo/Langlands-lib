# The different and the sum over the lower filtration

`Langlands.LocalFactor.Ramification.DifferentFiltration`. For a group `G` acting on a local ring
`B`, the module defines the sum of `|G_i| - 1` over the lower filtration and the proposition that
the different ideal of `B` over a subring `A` is the corresponding power of the maximal ideal
(Hilbert's formula). The proposition is stated, not proved: it is the target of a statement layer,
and nothing in the Library uses it yet.

## Statements

Name space `Langlands.Ramification`; `B` a local ring with `[MulSemiringAction G B]`.

- The filtration sum and the per-element count:

  ```lean
  noncomputable def lowerGroupFiltrationSum (N : ℕ) : ℕ :=
    ∑ i ∈ Finset.range N, (Nat.card (lowerGroup B G i) - 1)

  noncomputable def lowerGroupDepthCount (N : ℕ) (σ : G) : ℕ :=
    ((Finset.range N).filter fun i => σ ∈ lowerGroup B G i).card
  ```
  (the second with classical decidability).
- Once `G_N = ⊥`, the sum does not change: `lowerGroup_eq_bot_of_le` (`G_N = ⊥` and `N ≤ M` give
  `G_M = ⊥`), `lowerGroupFiltrationSum_eq_of_le`, `lowerGroupFiltrationSum_eq_of_eq_bot`.
- Counting by elements, for finite `G`:

  ```lean
  theorem sum_lowerGroupDepthCount_erase_one [Fintype G] [DecidableEq G] (N : ℕ) :
      (∑ σ ∈ Finset.univ.erase (1 : G), lowerGroupDepthCount B G N σ)
        = lowerGroupFiltrationSum B G N
  ```
- The proposition, for a domain `A` and a local Dedekind domain `B` that is a torsion-free
  `A`-algebra:

  ```lean
  def DifferentEqPowFiltrationSum : Prop :=
    ∀ N : ℕ, lowerGroup B G N = ⊥ →
      differentIdeal A B = IsLocalRing.maximalIdeal B ^ lowerGroupFiltrationSum B G N
  ```
  and `differentEqPowFiltrationSum_of_cutoff`: it suffices to know the equation for one `N` with
  `G_N = ⊥`.

## Proofs

The terms `|G_i| - 1` vanish from the first trivial group on, so the sums over `range N` and
`range M` agree; the element count is the exchange of the two finite sums, using that `σ ≠ 1`
lies in `G_i` exactly `|G_i| - 1` times among the non-identity elements.

## Declarations

In the order of the file: `lowerGroupFiltrationSum`, `lowerGroupDepthCount`,
`lowerGroup_eq_bot_of_le`, `lowerGroupFiltrationSum_eq_of_le`,
`lowerGroupFiltrationSum_eq_of_eq_bot`, a private lemma `sum_erase_one_ite_mem`,
`sum_lowerGroupDepthCount_erase_one`, `DifferentEqPowFiltrationSum`,
`differentEqPowFiltrationSum_of_cutoff`.

## Source and licence

Adapted from one file of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Definitions/Def_DifferentFiltrationFormula.lean` | `f4140b0dab073df7fae997a7b880481bae25bd05f7fc33ed84ad48dc92355ede` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list this file as containing third-party material. The Lean file begins with an attribution header
stating that it was modified.

Changes against the FLT file: statements are on `lowerGroup`; the FLT root names
`lowerRamificationFiltrationSum`, `lowerRamificationDepthCount`, `DifferentEqPowFiltrationSum`, …
are `Langlands.Ramification.lowerGroupFiltrationSum`, `lowerGroupDepthCount`,
`DifferentEqPowFiltrationSum`, …; the FLT file's local instance `FractionRing.liftAlgebra` is kept; no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter IV, §1, Proposition 4, printed page 64: for a finite
Galois extension `L/K` with Galois group `G`, `K` complete under a discrete valuation and the
residue extension separable (the hypotheses of the chapter, printed page 61),
`v_L(𝔇_{L/K}) = ∑_{s ≠ 1} i_G(s) = ∑_{i ≥ 0} (|G_i| - 1)`. Here `B` is any local Dedekind domain
with a group action, and the proposition is only stated.
