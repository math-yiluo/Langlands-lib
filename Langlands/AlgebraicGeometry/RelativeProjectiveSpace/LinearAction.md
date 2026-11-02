# Projective linear actions over arbitrary scheme bases

Let `S` be an arbitrary scheme, `K` a commutative ring, and
`a : S ⟶ Spec K` a morphism. `toPolynomial n a` projects the actual
relative projective space over `S` to the polynomial projective space
over `K`. It uses the existing affine comparison isomorphism.
Its composites with the structural map and the map to the integral model
are the expected projections.

`liftOverPolynomial` combines a base map `p : X ⟶ S` and a morphism
`q : X ⟶ ProjectiveSpace K n` compatible over `Spec K`. It is an actual
morphism to relative projective space whose two projections recover `p`
and `q`. Those projections determine a morphism uniquely.

`linearAction a e` is the actual relative scheme endomorphism obtained
by lifting the base projection and the polynomial projection followed
by the existing projective action of an invertible linear map
`e : K^(n+1) ≃ₗ[K] K^(n+1)`. It preserves the base projection and
acts on the polynomial projection by that projective action. The identity,
composition and inverse laws follow, so `linearActionIso` is an actual
scheme isomorphism. The order of composition is covariant:
applying `e` and then `f` gives `e.trans f`.

These actions commute with arbitrary changes of the scheme base over the
same coefficient ring. A scalar unit induces the identity on the entire
relative scheme, including its structure sheaf.

This is an internal derived construction. The lifting formulas follow
from the existing affine comparison and the universal property of relative
projective space. The action identities follow by the two-projection
extensionality lemma and the existing identities for the actual polynomial
projective action. No additional external source assertion is used.
This unit constructs coefficient linear actions; it does not construct a
projective bundle for a nontrivial locally free sheaf or a moduli quotient.
