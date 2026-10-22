# Regrouping restricted series by one variable

Author: Worker 56.

Mathlib's genuine formal-series equivalence groups the exponent of coordinate
zero in `Fin (n+1)` and keeps the remaining coordinates in `Fin n`. This file
constructs each coefficient slice in the actual smaller Tate algebra:
restrictedness follows by composition with the injective exponent inclusion.
The slice norms tend to zero because every positive coefficient superlevel set
is finite and the coefficient norm in each slice is attained. Thus the
regrouped object is an actual restricted series over the smaller Tate algebra.
Coefficientwise bounds in both directions show that grouping preserves the
Gauss norm.

Conversely, formal ungrouping is restricted because there are finitely many
large slices, each of which has finitely many large coefficients. These
constructions are inverse. Forgetting the restrictedness proofs gives an
injective map into formal power series; Mathlib's formal-series equivalence
then proves addition and multiplication compatibility. `regroupEquiv` is the
resulting actual ring equivalence, and `regroupEquiv_isometry` proves it
preserves the metric. `regroup_algebraMap` proves compatibility with the two
constant-series maps, explicitly, without installing an additional
scalar-tower instance.

The code does not assume the regrouped equivalence as input. Its coefficient
ring is an arbitrary ultrametric normed commutative ring; completeness,
nontriviality, norm multiplicativity and a field structure are not needed.

Source: retained Berkovich-course notes, Section 2.2, page 4, immediately
before Proposition 2.2.5, where a Tate algebra is treated as restricted series
over the smaller Tate algebra. Our chosen coordinate is zero, as in Mathlib's
`MvPowerSeries.finSuccEquiv`, rather than the notes' last-coordinate notation.
Only radius one is treated.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
