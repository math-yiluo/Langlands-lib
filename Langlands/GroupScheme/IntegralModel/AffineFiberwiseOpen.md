# Affine fibrewise closed opens in integral Dedekind models

This internal supporting unit studies one actual affine flat model over a
Dedekind domain and opens in its total space. It makes no reductivity claim.

An integral generic group gives an integral total space: the generic
projection is quasi-compact and schematically dominant, so its map on
global sections is injective. The target is affine and its section ring
therefore embeds into the domain of generic sections.

A nonzero element of a Dedekind domain is contained in only finitely many
prime ideals. Each such prime is a minimal prime over its principal ideal,
because a nonzero prime is maximal. Noetherian finiteness of minimal primes
gives the result, including the case of an empty zero locus.

For an affine scheme locally of finite presentation over this base, an
open containing the entire generic fibre contains the inverse image of a
nonzero principal open. The image of the closed complement is constructible
by Chevalley's theorem. Constructible membership is constant near the
generic point; since that point is outside the image, a basic open
neighbourhood avoids the complement.

Suppose in addition that the total space is integral and smooth over the
base, and the given open is closed in every underlying fibre. Its
intersection with the inverse image of the chosen principal open is the
whole principal open. Its intersection with the complementary divisor is
a finite union of closed subsets of closed fibres. The principal open is
dense because smooth morphisms are open, and integrality supplies
irreducible open neighbourhoods. The published
`FibrewiseClopenAffineOpen` criterion now proves that the open is affine.

This extends the internal affine-open argument used by
`SmoothDvrAffineOpenGeometry` to a Dedekind base with integral total space
and an open containing the generic fibre. All hypotheses are retained
explicitly; the unit does not prove affineness for arbitrary opens or
for arbitrary relative identity components.
