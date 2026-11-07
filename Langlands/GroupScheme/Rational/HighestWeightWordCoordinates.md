# Full opposite-root coordinates and the original highest-weight coefficient

Work over a field `k : Type u` with an affine group scheme and a supplied split
pinning `p`. Define `linkedSimpleLoweringMap` to be the negative map of the linked
full-root parametrization for each simple root. This choice retains the entire
intrinsic root functor and the literal rank-one relation on every relative test
scheme.

Rational conjugation preserves monicity. For supplied actual rational
simple-reflection representatives, the word construction conjugates each simple
lowering map by the actual tail product. Its previously proved full-torus
equivariance and the monic-root uniqueness theorem therefore identify every
conjugated factor with the entire successive negative intrinsic root functor.
This comparison applies to arbitrary words and does not require a representation.

Reducedness of the pinning's root datum makes positive integral root rays unique.
The proof converts a positive-multiple equality to linear dependence of the two
roots. Reducedness makes the roots equal or opposite; torsion freeness then
identifies the two multiplicities or excludes the opposite case.

Assume also that the root index is finite and that the integral coroot span is
full. Polarize integral rho. For a word enumerating every positive root exactly
once, the negatives of its successive roots enumerate exactly the roots positive
on negative polarized rho. The existing `SplitBigCell.orderedProduct_points`
theorem applies to the full root representations above. It proves injectivity
and exact image equal to the opposite polarized-rho unipotent subgroup on every
relative test scheme, including nonreduced ones. The product uses the maps as its
index set and the list's `get` function as its position map, preserving the
original order and arbitrary universe `u`.

For the coefficient conclusions, assume `k` is infinite and supply a finite
matrix representation satisfying `p.IsHighestWeight` at `m rho`. This predicate
includes irreducibility, complete weight decomposition, dimension one of the
highest space and lower-weight support. The fixed linked simple maps retain the
all-test rank-one relation. Integral rho supplies the simple-coroot pairings and
positivity, so the original highest-weight endpoint and word telescoping theorem
identify the constant-degree word coefficient with a unit scalar times the
actual rational word matrix applied to the highest vector. Its nonvanishing
follows from invertibility of that matrix and a nonzero highest vector.

The final `exists_highestWeight_wordCoordinates` theorem obtains the actual
simple-reflection representatives and a positive word from the supplied pinning.
One such word simultaneously gives the all-test coordinates and a nonzero
original ordered polynomial coefficient at every exponent tuple constantly equal
to `m`, for every nonzero highest vector. The existing ordered-coefficient
comparison preserves the factor order; no independent translation action is
assigned to the noncommuting coordinates.

This is an internal composition of the linked-root, monic-root, positive-word,
word-endpoint and split-big-cell Library constructions. It assumes the pinning
and highest-weight representation. It supplies neither their existence nor a
dimension bound or irreducibility proof for the entire induced space, and does
not prove the full `SteinbergBigCellStatement`.
