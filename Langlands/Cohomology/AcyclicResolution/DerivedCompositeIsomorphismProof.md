# The derived composite comparison is an isomorphism

`derivedCompositeIsomorphism` proves the exact proposition
`DerivedCompositeIsomorphismStatement`, retaining all nine independent universes.
This is an internal deduction from the existing derived comparison and degreewise
acyclic-resolution criterion.

Mathlib's `DerivedCategory.isIso_iff` reduces invertibility of the actual map to
invertibility of its map on every integer cohomology object. In a negative
degree, `DerivedPlus.isZero_homology_of_neg` proves both the source and target
cohomology objects zero. Every morphism between zero objects is invertible.

For a nonnegative degree, write it as a natural number `n`.
`isIso_compComparison` proves invertibility of the degreewise comparison using
left exactness of `G` and the stated acyclicity of `F(J)` for each injective `J`.
`derivedCompComparison_homology` identifies the actual cohomology map, followed
by the specified target homology isomorphism, with the specified source homology
isomorphism followed by that degreewise comparison. This composite is therefore
invertible. Cancellation of the target isomorphism proves invertibility of the
actual cohomology map and finishes the derived-category criterion.

The proof uses the specified canonical map and its actual cohomology formula.
It establishes no geometric base change or cube theorem.
