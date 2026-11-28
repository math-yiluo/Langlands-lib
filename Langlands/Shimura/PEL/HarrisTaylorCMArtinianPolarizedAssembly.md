# Assembling a polarized rational lift from actual geometric lifts

The lower representative is transported to the specified actual reduction
by the given isomorphism of abelian schemes. The transported polarization
is its integral dual pullback. Integral lifts of nonzero multiples of the
transported action on a rational basis produce the entire thicker rational
action by `exists_rationalAction_of_basis_lifts`. Faithfulness follows by
restricting and using the faithfulness of the transported action.

The hypothesis identifying the reduction of the thicker polarization
transports the rational involution equation. The canonical dual square
and surjective-base-change rigidity reflect this equation to the thicker
representative.

The polarization comparison initially uses one chosen evaluation on the
actual reduction. Applying canonical dual naturality to the identity
morphism compares it with any other evaluation on that scheme. The dual
composition law identifies the new comparison with the pullback along
the original integral isomorphism. Rationalization gives the required
equation with multiplier one for every evaluation.

`positivePolarizedAction_lifts_of_integral_map_lifts` clears denominators
simultaneously for the images of a finite rational basis on the original
representative. The geometric lifting condition is then an integral
restriction equation for each of those endomorphisms and an equation
for the given integral polarization. Cancellation of the marked
isomorphism after rationalization gives the basis equations used by the
assembly.

For an elementary extension, the maximal-ideal condition implies that
the kernel is square-zero. The map of spectra is surjective, and
`DualWitness.isPolarization_of_squareZero_reduction` gives positivity
of any actual thicker dual-valued homomorphism whose reduction is the
specified transported polarization. The strengthened assembly
`positivePolarizedAction_lifts_of_integral_map_lifts_elementary` therefore
uses only integral morphism-lifting equations on the thicker scheme.
