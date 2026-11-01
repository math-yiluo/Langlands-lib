# Closed maximal-stalk points and exact-dimensional ample cuts

This module proves the published target `AmpleSectionExactDimensionStatement`
by combining `exists_closedPoint_stalk_dim_eq` and
`exists_ampleSection_exact_dimension` in its final theorem
`ampleSectionExactDimension`.

The first helper obtains an irreducible-closed chain of length `d` from the
finite global dimension. Quasi-compactness supplies a closed point in its
smallest member. Coheight is antitone under inclusion, so that point's
coheight is at least the chain length. Every coheight is at most the global
Krull dimension, giving equality. The identification of actual scheme stalk
dimension with point coheight completes this part.

The intermediate helper `lineBundle_stalk_dim_le_vanishing_add_one` works on
any locally Noetherian scheme and at any point outside a line-bundle
section's entire generation open. On a local frame, the section becomes a
scalar coefficient. `localFrame_basicOpen_coeff` identifies its basic open
with the pullback of the original generation open, so the coefficient germ
is a nonunit. The Noetherian local principal-quotient inequality bounds the
local dimension by one plus the quotient dimension. The quotient spectrum
embeds into the local basic-open complement; that local complement embeds
into the original vanishing set. Monotonicity gives the claimed lower bound
for the latter's dimension plus one. The open immersion identifies the two
stalk rings.

For the ample-cut construction, choose a closed point of maximal stalk
dimension. Positive global dimension rules out a one-point space, supplying
a different point. Apply `ampleSectionOpenBasis` to the complement of the
chosen closed point at that different point. The resulting section of a
positive tensor power has nonempty generation open and vanishes at the
chosen point. Irreducibility and the proper-closed-subset inequality give
one dimension bound; the local helper at the chosen point gives the other.

This is an internal geometric proof, with no external source translation.
It uses the actual module, stalk and generation-open constructions. It does
not require the chosen point to be rational or every closed stalk to have
the full dimension. No regularity of the section, Cartier subscheme,
generic-length devissage, or Euler positivity conclusion is asserted.
