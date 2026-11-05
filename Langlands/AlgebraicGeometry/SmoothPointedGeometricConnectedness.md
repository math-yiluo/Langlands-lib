# Geometric connectedness of smooth connected pointed field schemes

This derived helper concerns a smooth scheme over an arbitrary field, with
connected underlying space and an actual section of its structure morphism.
It imposes no quasi-compactness or affineness assumption.

`sectionFiberIso` is the actual scheme isomorphism identifying the pullback of
a base-change projection along a section with the new base scheme. It composes
the iterated-pullback comparison, the section equation, and the pullback
isomorphism for an identity morphism. It is defined for arbitrary schemes.

The proof first establishes a topological observation: an open and closed map
to a connected space, with a nonempty singleton fibre, has connected source.
Indeed, images of a nontrivial clopen partition would both be the whole target
and would split the singleton fibre.

For the projection from the algebraic-closure base change, openness follows
from universal openness of morphisms to field spectra. Closedness follows from
integrality of the algebraic closure. The fibre over the rational section point
is a singleton: its scheme pullback is the spectrum of the algebraic closure.
The iterated-pullback comparison generalizes the section-fibre calculation in
the Library's ported FLT
`S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`
module, `subsingleton_pullback_one_fst`; the present argument requires no group law.

The base change is consequently connected. Its smoothness supplies local
Noetherianity and domain stalks, so the published
`connectedLocallyNoetherianDomainStalksIntegral` makes it integral.
The published geometric irreducibility theorem over an algebraically closed
field then gives geometric connectedness there. Finally the published
surjective base-change descent theorem gives geometric connectedness over the
original field.

This is internal derived content, using the named Library results and
Mathlib's actual scheme pullbacks, integral morphisms, and universal openness.
It is a helper for the relative identity-component existence proof.
