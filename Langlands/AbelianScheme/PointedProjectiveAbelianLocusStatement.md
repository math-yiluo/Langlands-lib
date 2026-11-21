# The abelian-scheme locus of a pointed projective family

`Langlands.AbelianScheme.PointedProjectiveAbelianLocusStatement` specifies an open
subscheme of a locally noetherian base `S` for a pointed flat, locally finitely
presented family. The family is given by a closed immersion `i` into relative
projective space, its projection `p`, and a section `s` of `p`.

For every locally noetherian test scheme `T` with `t : T ⟶ S`, the image of `t`
lies in the open if and only if `X ×ₛ T` admits an abelian-scheme structure of
the prescribed relative dimension `g`, with identity the section induced by `s`.
`HasPointedAbelianPullback` spells out this condition with a scheme isomorphism
over `T`. The equality after projection to `X`, together with the equality over
`T`, identifies the two sections by the pullback property. The open inclusion
itself is a test morphism, so the statement also supplies a structure over the
locus.

This is a consequence of the smooth connected locus and the abelian-scheme
locus in Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed.
(1994), Proposition 6.16 and the proof of Proposition 7.3, steps (I) and (II).
The relative dimension refinement amounts to restricting the locally constant
smooth relative dimension at the identity section. Proposition 6.16 gives
openness, which suffices in the construction of the relative Hilbert locus.
The source also obtains clopenness inside the smooth connected locus using
Theorem 6.14.

The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
printed pp. 126–127 and 133 (PDF pp. 139–140 and 146).
