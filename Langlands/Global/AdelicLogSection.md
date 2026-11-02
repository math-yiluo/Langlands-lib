# An actual adelic logarithm section from character restriction

Author: Worker 112.

For a number field `F`, an actual group scheme `G`, an actual commutative group
scheme `T`, and an actual homomorphism `i : T.toGrp ⟶ G`, this module constructs
a continuous section of the normalized adelic character logarithm. The inputs
are a supplied finite split-torus isomorphism for `T`, injectivity of the actual
rational-character restriction `characterRestrict i`, and finite index of its
actual range. The algebraic general reductive theorem providing the latter two
inputs remains separate.

The existing positive-torus logarithm is a topological group equivalence from
the intrinsic positive subgroup of the actual adelic points of `T` onto its
entire real character dual. The continuous real-dual restriction equivalence
carries that dual to the dual of `G`. Their composite is
`positiveAmbientLogEquiv`. Its forward function is exactly the normalized
ambient logarithm of the actual point image under `i`, by naturality of the
character logarithm. The topology is the existing pointwise topology on all
actual rational characters, without a separately chosen topology or character
basis on `G`.

Invert this composite and apply the actual continuous adelic point map of `i`.
The resulting `logSection` is a continuous group homomorphism from the
multiplicatively written additive real dual into the actual group `G(A_F)`.
Its composite with the ambient logarithm is the identity. Consequently the
ambient logarithm is surjective. Its range as a subgroup is exactly the existing
`imageSubgroup` of the intrinsic positive subgroup, and the section recovers
each point in that image. In particular the positive point map is injective
even though no independent scheme or topological embedding hypothesis is used.
The actual positive image intersects the actual norm-one subgroup only in the
identity.

## Provenance and scope

This is a derived adapter for MW95, I.1.4, printed pp.5–7, especially the
finite-index character-restriction argument on p.6 and normalized logarithmic
pairing (4) on p.7. The actual equal-archimedean scalar realization is the one
used in I.2.1, printed pp.18–20. Source ID
`moeglin-waldspurger-1995-spectral-decomposition`, folder SHA-256
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`.
The implementation composes the existing explicit positive exponential, whose
scalar coordinates divide by `[F:Q]`, with the index-normalized real-dual
extension. Both normalization factors remain in those actual maps.

The results apply to any supplied morphism with these hypotheses. They do not
assert that `T` is central or maximal, that `G` is reductive, that the
finite-index inputs hold for a general split component, or that either of the
needed algebraic objects exists. No measure, Iwasawa, reduction, or finite-volume
assertion is made. Empty finite torus rank is allowed.
