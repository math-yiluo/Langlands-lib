# Standard rational covers from finite tuples

Author: Worker 575.

For an ultrametric normed field `K : Type u`, a presented strict affinoid algebra
`P`, and a tuple `f : Fin n → P`, assume
`h : ∀ x : BanachSpectrum P, ∃ k, x (f k) ≠ 0`. For each `j : Fin n`,
`Langlands.Analytic.StrictTestDomain.standardRational f h j` is a
`RationalData K P` with arity `n`, denominator `f j`, and numerator tuple `f`.
The projection lemmas `standardRational_arity`, `standardRational_denominator`,
and `standardRational_numerator` identify these fields. Its
`RationalData.no_common_zero` proof is the right disjunct `h x` at every point:
some numerator is nonzero regardless of the chosen denominator.

Over a complete coefficient field, apply the existing `RationalData.algebra`
and `RationalData.baseMap` to this datum. These give the actual closed-ideal
Tate quotient
`RationalLocalization.algebra K P n (f j) f` and its bounded structural map
`RationalLocalization.baseMap K P n (f j) f`. Thus the construction uses the
existing equations `(f j) * Y_k = f k` for all `k : Fin n`.
In particular, it intentionally retains the redundant `j`-th numerator and
the associated coordinate, in accordance with the existing rational quotient
convention. It introduces no auxiliary algebra or replacement restriction maps.

The theorem `mem_standardRational_locus` is the exact formula
`x ∈ (standardRational f h j).locus ↔ ∀ k, x (f k) ≤ x (f j)`.
The self-inequality for `k = j` imposes no further condition.
The theorem `standardRational_covers` proves that for every spectrum point `x`
there is such a `j`. Its implemented proof first takes an index from `h x`,
making the finite index set nonempty locally at `x`, and then uses
`Finset.exists_max_image` to choose a maximal value among the real numbers
`x (f k)`. The resulting maximality inequalities are precisely membership in
that standard locus.

No nonempty-tuple assumption is imposed. For `n = 0`, the existence demanded
by `h x` is impossible, so `h` rules out every spectrum point. The cover
assertion therefore also holds for the empty tuple and empty spectrum. Zero
and nonreduced bases are permitted; no reducedness, nonzero-algebra assumption,
or spectral injectivity is used.

For an actual bounded `K`-algebra map `φ : BoundedAlgHom K P Q`,
`tuple_no_common_zero_pullback` proves the same nonvanishing condition for
`fun k => φ (f k)` by applying `h` to
`BanachSpectrum.comap φ.toBoundedRingHom x`. The theorem
`standardRational_pullback` identifies the standard datum of the mapped tuple
with the existing `RationalData.pullback φ`.
The theorem `standardRational_locus_pullback` gives the corresponding equality
with the inverse image of the original locus. These equalities follow from
the fields of the data, proof irrelevance, and evaluation of the pulled-back
seminorm. Quotient comparison maps and restriction maps remain the existing
ones attached to rational data.

The source construction is Achinger, *Introduction to non-Archimedean Geometry*
(November 22, 2020), Definition 7.2.1, printed/PDF p.65. The retained source is
registered as `achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
Achinger uses a tuple indexed from `0` through `n`, generating the unit ideal,
and the associated rational domains of the rigid spectrum. Here the tuple
length is `n`, and its hypothesis is absence of common zeros on the Banach
spectrum. The existing
`Langlands.Analytic.RationalFactorization.generatesUnitIdeal_iff_no_common_zero`
connects the unit-ideal and spectrum conditions for rational input over a
complete coefficient field. Applied with any selected denominator `f j` and
the whole tuple of numerators, it gives unit-ideal generation from the right
disjunct `h`. No separate unit-ideal input is required by this constructor.

This module's use of Berkovich spectra and allowance of trivial scalar
valuation are derived extensions, rather than a quotation of Achinger's
scope: his standing convention on p.6 requires nontrivial valuation.
Berkovich, *Non-Archimedean analytic spaces* (Trieste lectures, 2009),
Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p.9, give the rational-domain
context in terms of elements with no common spectrum zero. This source is
registered as `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The extension here uses only the defining rational inequalities, a maximum of
finitely many real evaluations, and the actual pullback of a spectrum point.
None of those arguments chooses a scalar of norm less than one or assumes a
nontrivial scalar valuation. In fact the data construction and elementary
laws do not require completeness; the existing quotient constructors apply
when `K` is complete.

This unit proves the explicit point cover and elementary pullback laws. It
does not assert finite refinement, analytic gluing, acyclicity, or the full
affinoid-domain universal property for arbitrary affinoid tests.
