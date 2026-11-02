# Finite tuple tails as open extensions

This is internal, derived infrastructure for the pushout step in Stacks
Project, Proposition 70.8.1, Tag 07SU, applied to the finite symmetric-tuple
presentation motivated by Tags 0BBN and 07ST. The registered source is
`stacks-noetherian-approximation-2026-11-01`. The proof uses the implemented
threshold invariance, complement source pullback, and open-extension
comparison and recovery results; it adds no approximation assumption.

All declarations are in
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`. The input is an
étale equivalence relation `E` in arbitrary universe `u`, with separated
source, affine object and arrow schemes, and closed joint endpoint map.
The finite tail has tuple indices `p ≤ i ≤ N`, with index `i`
representing tuples of length `i + 1`.

`tupleTailNextOpen N p` is the threshold `p + 1` in the object scheme of
the whole tail. `tupleTailNextOpen_isInvariant` reverses the existing
equality of target and source threshold inverse images.
`tupleTailNextRelation` restricts the whole tail to this open, and
`tupleTailNextRelation_isCartesianHom` supplies its actual cartesian
inclusion into the tail. The old open in this construction is the
invariant threshold, whose source pullback was proved; it is not merely
the selected family of higher tuple charts.

`tupleTailNextComplement_covers` proves point coverage of the complement
by the canonical closed complement scheme. It rewrites the range of the
open inclusion as the open itself and the range of the complement
inclusion as the complementary closed set. It asserts no factorization
of arbitrary test schemes through that closed scheme.

`tupleTailOpenExtension` extends the next-threshold restriction by the
identity on the full tail object scheme. For `p < N + 1`,
`tupleTailOpenExtensionArrowsIso` identifies its pushout arrow scheme
with the actual finite-tail arrow scheme. It applies recovery to the
cartesian invariant-open inclusion, the preceding point coverage, and
`tupleTailNextComplement_unit_isPullback`. The four endpoint equations
for the isomorphism and its inverse are the recovery equations.
`tupleTailOpenExtension_isCartesianHom` specializes the forward recovery
result, with identity object map. Its inverse is cartesian too:
`tupleTailOpenExtension_inv_isCartesianHom` proves the source pullback
directly. The arrow isomorphism gives uniqueness, and composing a cone
with its forward map gives the required lift.

Finally, suppose the next-threshold restriction has a cartesian map
`(a,b)` to a relation `F`. Let `κ : F.U → V` be an open immersion and
`v` a map from the full tail object to `V`, with a pullback square
`IsPullback a nextOpen.ι κ v`. `tupleTailToOpenExtension` constructs the
arrow map to the extension of `F` along `κ`: it composes the inverse
recovery isomorphism with the actual pushout comparison.
`tupleTailToOpenExtension_isCartesianHom` composes the two proved
cartesian maps, and `tupleTailToOpenExtension_t` and
`tupleTailToOpenExtension_s` give its endpoint equations. The cartesian
map on the open and the open pullback square are explicit input data;
the construction proves the resulting full-tail source pullback.

These results perform the finite-tail recovery and compatible-level
pushout comparison. They do not construct the required chart change,
finite type open model, or final Noetherian first level.
