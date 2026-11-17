# Open-local root-datum character formulas after base change

This internal derived module converts the monomial formula in the explicit
`AffineSplitSurjectionRootDatumStatement` hypothesis into equalities of actual
coordinate-torus characters after arbitrary scheme base change. It is a step
towards assembling local conjugators over an arbitrary base ring. The intrinsic
proposition remains an explicit hypothesis.

`HasZariskiLocalRootDatumTorusCharacterMap tau P Q` is a Prop-valued predicate
over an arbitrary commutative ring R. At every point of Spec R it supplies an
open neighbourhood V, a natural number p and a root-datum isogeny from Q to P.
For every scheme B with a map b to Spec R whose inverse image of V is the whole
of B, the coordinate pullback of tau carries each target exponent character to
the source exponent character specified by the same weight map. The root-datum
isogeny and p may depend on the neighbourhood. This predicate does not retain
the characteristic-vanishing clause or the connected-base clause of the
intrinsic proposition.

The first three lemmas work over any pair of schemes S and S', with b from S'
to S. `splitTorus.pointsEquiv_baseChangeIso_inv` identifies coordinate points
through the inverse canonical split-torus pullback isomorphism. Its proof
applies the existing forward-coordinate lemma and cancels the inverse and
forward isomorphisms. `splitTorus.pointsEquiv_coordinateBaseChangeHom` then
computes the coordinate pullback of a torus homomorphism by transporting the
point to the original base and applying the original homomorphism. Its proof
uses the forward-coordinate lemma and naturality of the group-scheme
base-change point equivalence.

`splitTorus.coordinateBaseChangeHom_character_of_open_points` assumes a
monomial identity on every test scheme over S whose image lies in an open V.
If the image of b lies in V, it proves an equality of actual characters over
S'. The proof uses group-scheme pointwise extensionality and the multiplicative
group point equivalence, evaluates exponent characters as products, and applies
the assumed identity to the original-base image of each test scheme over S'.
The inverse-coordinate lemma identifies its source coordinates.

`hasZariskiLocalRootDatumTorusCharacterMap_of_affineSplitSurjectionRootDatum`
applies the local clause of the explicit intrinsic proposition and then this
character-equality lemma. Its premises include actual reductive groups, closed
fibrewise maximal coordinate tori, supplied fibrewise root data, free root
weight spaces, and a locally quasi-finite surjective group-scheme homomorphism
with the stated torus square. There is no local-ring hypothesis. Root data and
root-space trivializations are still supplied. The result supplies local
character formulas; it does not construct a cover, normalized root maps or
conjugators and does not prove the unconditional rigidity target.

The provenance is direct derivation from the existing canonical split-torus
base-change isomorphisms, their point-coordinate formulas, exponent-character
evaluation, pointwise extensionality, and the local clause of the explicitly
assumed intrinsic proposition. No additional source theorem is asserted.
