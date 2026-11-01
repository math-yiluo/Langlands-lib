# Uniform scalar thresholds and degenerate cases for rational descent

Authors: Worker 146 and Worker 101. Worker 146 supplied the six elementary
preparation proofs in revision 4 of the unreviewed whole-spectrum draft.
Worker 101 extracted them into this module, allowed an independent universe
for the cover index, and added the chosen scalar and empty-standard-cover
specialization.

This module constructs `scalarUniformThreshold` and proves elementary
preparation lemmas. It does not prove standard-cover descent.

## The scalar construction

For a normed ultrametric field `K`, a presented strict affinoid algebra `P`,
and a tuple `f : Fin n → P` with

```lean
hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0
```

`exists_positive_uniform_threshold f hf` produces a real `ε > 0` such that
at every point `x` some entry satisfies `ε < x (f j)`. Completeness of `K`
is not needed for this lemma.

If `Fin n` is nonempty, the proof uses the function

```lean
F x = Finset.univ.sup' Finset.univ_nonempty (fun j => x (f j))
```

The evaluation maps are continuous, so their finite maximum is continuous.
Nonnegativity of spectrum evaluations and `hf` make this maximum positive.
Compactness of the Banach spectrum gives a positive uniform lower bound;
half that bound is strictly below some entry at each point. If `Fin n` is
empty, `hf` makes every purported spectrum point impossible, and `ε = 1`
satisfies the assertion. The proof does not assume a nonempty spectrum.

Given the additional explicit hypothesis

```lean
hK : ∃ c : K, 1 < ‖c‖
```

`exists_scalar_uniform_threshold hK f hf` produces a scalar `c ≠ 0`
satisfying

```lean
∀ x : BanachSpectrum P, ∃ j, ‖c‖ < x (f j)
```

The proof installs a `NontriviallyNormedField K` structure with the existing
normed-field structure and witness `hK`. Mathlib's
`NormedField.exists_norm_lt` then supplies a nonzero scalar whose norm is
below the positive real threshold.

The primary construction `scalarUniformThreshold hK f hf` chooses such a
scalar. Its result type is the subtype

```lean
{c : K // c ≠ 0 ∧ ∀ x : BanachSpectrum P, ∃ j, ‖c‖ < x (f j)}
```

Thus both properties are available directly from the result's `.property`.
The construction is noncomputable and does not select a canonical scalar.
Neither threshold lemma nor this construction requires completeness of `K`,
a nonzero or reduced base, units among the entries, or `0 < n`.

## Degenerate covers and denominator generation

The remaining lemmas assume `CompleteSpace K` and permit a cover index
`I : Type v` independent of the coefficient/base universe `u`.

`subsingleton_of_empty_whole_cover D hc` proves that an empty point-cover
of the whole spectrum forces `P` to be a subsingleton. Otherwise the
published `PresentedStrictAffinoidAlgebra.spectrum_nonempty` gives a point;
`hc` would assign it a member of the empty index type.
`existsUnique_whole_gluing_empty D hc s` then gives the actual unique scalar
lift, with the restriction equations vacuous.

`existsUnique_standard_gluing_empty f hf s` specializes this to `Fin 0`
using the published `standardRational_covers`. Its conclusion uses exactly
the actual `standardRational` algebras and base maps. It needs no compatibility
assumption because there are no entries.

`existsUnique_whole_gluing_of_subsingleton D s` handles a zero base and any
index type. Each actual quotient is a subsingleton because its unital base
map takes `0 = 1` to `0 = 1`. The base element `0` therefore has all prescribed
images and is unique. Empty rational loci and tuples cause no exception.

Finally, `span_denominators_eq_top_of_whole_cover D hc` proves that the
denominators of any whole-spectrum point-cover generate the unit ideal.
If their span were proper, the published
`PresentedStrictAffinoidAlgebra.exists_spectrum_kernel_of_proper_ideal`
would give a spectrum point annihilating every denominator. Covering that
point contradicts the published denominator nonvanishing on a rational
locus. Neither a finite index nor nontrivial scalar valuation is used.

## Provenance and scope

The threshold argument implements the compactness step in Piotr Achinger,
*Introduction to non-Archimedean Geometry*, November 22, 2020, §7.3,
printed/PDF p.67: a finite tuple without common zeros admits a uniformly
small nonzero scalar before the Laurent split. The source works with
the maximal spectrum and a power of a pseudouniformizer; this module uses
the compact Banach spectrum and Mathlib's small-scalar theorem. Achinger's
nontrivial valuation convention is on p.6. The retained original is
registered as `achinger-2020-non-archimedean-geometry-nov22`:

`/home/taskhub/pilot/literature/Piotr Achinger, Introduction to non-Archimedean Geometry (November 22, 2020).pdf`

SHA256:
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.

The empty-cover and zero-base proofs, arbitrary-index denominator argument,
and subtype packaging are internal consequences of the cited published
Library lemmas. They are included to preserve degenerate cases in the
later standard-cover induction. No source-specific errata note was found
in the project literature or public notes when checked on November 1, 2026.

The actual rational quotient carriers, base maps and spectrum are unchanged.
This unit proves no descent for a nonempty cover over a nonzero base,
Laurent-cover comparison, refinement transfer, higher Čech exactness,
admissibility, finite-module descent, arbitrary-radius descent or sheaf theorem.
