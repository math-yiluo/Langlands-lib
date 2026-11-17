# Actual test-comparison naturality for successive coefficient extension

This internal unit proves the actual successive-coefficient atlas isomorphisms
intertwine the test comparisons of a specified full-order refined comparison.
The old, intermediate and final finer chart choices need not agree.

The proof first extracts the complete formal-coordinate equation from the
previous coefficient-extension isomorphism equality. The outer-transition
law for actual test comparisons follows from the two original transition
cocycles. Applying the coefficient equation twice identifies the iterated
comparison with the original comparison on its restricted test. Applying it
once identifies the direct comparison. The actual coefficient-composition
chart maps are the original transitions between the iterated and direct
selected source charts. The outer-transition law therefore proves the whole
integral square by full formal-map extensionality and inverse uniqueness.

`baseCompTestSquare` rationalizes the four specified integral maps and packages
the proved equation. Its proof uses preservation of integral composition under
rationalization in the actual ambient tensor Hom and full-order centralizer.
Both actual rational inverses come from the given integral isomorphisms.

All supplied finer and outer chart generators carry actual unit evidence.
Coefficient and order rings have separate universes, coordinates are arbitrary
finite types and covers may be infinite. Coefficient maps may merge generators. Rationalization also assumes the
coefficient order is a domain and the indicated field is its fraction field.
Supplied target scalars and commuting coefficient squares remain further
constructions; no framed comparison base change is asserted here.
