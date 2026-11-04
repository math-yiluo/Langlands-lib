# Finite positive covers of the actual dominant valuation image

Author: Worker 1292.

This internal derived development uses Dickson's lemma on the natural floors
of the actual positive-root orders. It retains the actual rational points,
integer character valuation, real centralizer valuation and uniformizer section.
The finite root support, finite index of the split valuation image, and
surjectivity of integer valuation from `C0` onto that image are explicit
premises of `exists_finite_positiveProductCover`. This module does not
establish those structural inputs.

The order lemmas choose the coordinatewise minimal elements of a set of
finitely many natural coordinates. They form an antichain, so Dickson's lemma
makes that set finite. Every vector has a minimal vector below it. Choosing
actual preimages gives a finite subset of the original set. Performing this
construction separately in each of finitely many residue classes preserves
the residue.

`dominantFloorCoordinates` records the natural floors of the real orders of
the positive relative roots. `nonneg_int_of_natFloor_le` proves that when two
nonnegative reals differ by an integer, ordering their natural floors orders
the original reals. This uses integer floor translation by an integer.

`dominantCentralizer_mul_mem` uses additivity of the real valuation and of
root evaluation to add the nonnegative orders.

The provenance is an elementary order and valuation argument. Dickson's lemma
is supplied by Mathlib's finite-product well-quasi-order instance and its
minimal-element theorem. The intended application is the finite positive
cover in Renard V.3.21–V.3.23 and V.5.1(4), using the positive-order convention
of the published `RenardDominantComparisonStatement`.

`exists_finite_positiveProductCover` applies the finite selection theorem to
actual dominant points, with residue `latticeResidue s` and coordinates
`dominantFloorCoordinates s h i ν`. For a dominant point `z`, it chooses a
selected dominant point `f` in the same residue, with no larger floors.
Equality of residues places the quotient of their integer valuation values
in `splitValuationImage s`. The assumed surjectivity supplies `c ∈ C0` with
that quotient as its valuation, so `c * f` and `z` have the same integer and
real valuation. Write `c` as the uniformizer value of a cocharacter `n`.
The normalization theorem in `RenardDominantValuation` says that every root
order of `c` is the integer pairing with `n`. Consequently the order of `z`
is the order of `f` plus that integer. The floor inequality proves that
integer nonnegative, hence `c ∈ C0Plus`. This constructs a positive product
representing every dominant valuation. Closure under multiplication proves
that all the positive products remain dominant.

The conclusion is exactly the imported `IsFinitePositiveProductCover`
predicate. It permits several selected points in the same residue class
and repeated valuation classes. The construction does not assert the
existence of a chamber-compatible transversal or any uniqueness of positive
products. Its conditional structural inputs must be supplied by published
theorems to prove the full `RenardDominantComparisonStatement`.
