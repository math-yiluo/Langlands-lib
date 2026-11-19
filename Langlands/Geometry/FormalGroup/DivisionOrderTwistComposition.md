# Composition of division-unit quasi-isogenies

For a finite-coordinate formal module with its actual integer-order action
`E`, this module proves the identity and composition laws for
`twistQuasiIsogeny`. Applying `g` and then `h` gives the twist by `h * g`.
The complete composite quasi-isogeny agrees with the map for `h * g` after
transport along that equality of target order actions.

`divisionConjugation` packages `d ↦ g⁻¹ d g` as a `K`-algebra automorphism
of the original division algebra `D`. It uses Mathlib's conjugation of a ring
by units and the centrality of the `K`-scalars. Its restriction to the
actual integer order is the existing `conjugation`. The rational extension
of the twisted action is the original rational action precomposed with
`divisionConjugation`, since the two algebra maps agree on the spanning
integer order.

Composition of the two forward tensors applies the rational action to
`(g⁻¹ h⁻¹ g) g⁻¹ = (h g)⁻¹`. Equality of the complete quasi-isogenies
then follows from inverse uniqueness. The identity law uses the image of
`1` in the endomorphism algebra. For a central scalar unit the forward
tensor is its inverse scalar times the rational identity.

These are the algebraic identity, product and scalar relations for the
inverse-conjugation part of the action in Drinfel'd, *Coverings of p-adic
symmetric regions* (1976), §2 A, printed p. 109. The framing heights and
the Frobenius correction require further results.
