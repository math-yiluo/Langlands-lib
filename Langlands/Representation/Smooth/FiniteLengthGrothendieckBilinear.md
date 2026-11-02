# Bilinear descent to the actual exact Grothendieck groups

This is an internal universal-property construction for the graded induction
product used in Aubert's Theorem 2.3. It extends the published
`FiniteLengthGrothendieckGroup.lift` construction in two variables; it is not an
additional representation-theoretic theorem from the literature.

The coefficient ring `R` is arbitrary commutative. The groups, their topological
spaces and all three representation carrier universes remain independent.
The objects and short exact sequences are precisely those of
`Smooth/FiniteLengthGrothendieck`, with length over the group algebra.

`lift₂` extends a function on two genuine finite-length isomorphism classes
when it is exact additive in each variable. The proof first lifts the right
variable, verifies the left exact relations by the published `hom_ext`, then
lifts the left variable. `bilinear_ext` compares two such bilinear maps on
actual finite-length object pairs.

For an actual bifunctor `Φ`, `PreservesFiniteLength₂` requires finite-length
output on finite-length pairs. `PreservesFiniteLengthShortExactLeft` and
`PreservesFiniteLengthShortExactRight` require that the actual mapped
intertwiners preserve every finite-length short exact sequence with a fixed
finite-length other factor. These are explicit premises, not proofs that an
arbitrary bifunctor is exact.

`mapClass₂` is well defined because `Φ` maps the product of two actual
categorical isomorphisms to an isomorphism. The two exactness premises give
the two exact-additive relations. `map₂` then constructs the integer-bilinear
map on the two exact Grothendieck groups. `tensorMap` uses the ordinary
tensor-product universal property. The object formulas give the actual
output class. No bijectivity, ring law, finite-length preservation or
representation isomorphism is asserted without its corresponding premise.

The implementation imports no classification, Jordan–Holder identification,
irreducible-image theorem, or Chapter V structural package. Its only
mathematical inputs are the published generic exact-K0 universal property,
functoriality of isomorphisms, and the module tensor-product universal
property. Applying it to normalized induction still requires the explicit
finite-length and two exactness facts for that actual bifunctor.
