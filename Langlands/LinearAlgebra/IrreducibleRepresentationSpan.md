# Burnside span and its matrix-action form

The proof applies the published `SandwichDimensionBound.action_surjective` to Mathlib's monoid-algebra module `Representation.asModule`. Its carrier and field-module structure agree definitionally with the original representation space. Surjectivity therefore gives a monoid-algebra preimage of each endomorphism. Monoid-algebra induction then shows that this endomorphism belongs to the span of the representation operators.

`matrixAction` is the natural representation obtained by applying the matrix-to-linear-endomorphism algebra equivalence to invertible matrices. The matrix span conclusion is transported through its underlying linear equivalence. These results have independent universes and no characteristic restriction; irreducibility already excludes the zero representation. This is a derived internal auxiliary and retains the host's group-scheme density and compactness obligations.
