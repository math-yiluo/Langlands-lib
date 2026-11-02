# Normalization and naturality of actual sheaf cohomology pushforward

This internal derivation supplies identities for the already published
`UnitSheafPushforward.cohomologyPushforwardEquiv`, for a topological isomorphism
`e : X ≅ Y` at every universe `u`. Coefficient sheaves take values in
`AddCommGrpCat.{u}`, and cohomology uses exactly Mathlib's `Sheaf.H.{u}`,
defined by Ext from the constant sheaf with coefficient `ULift ℤ`.

`cohomologyPushforwardEquiv_apply` expresses the existing equivalence as the
inverse exact-adjunction Ext equivalence followed by precomposition with the
inverse of the published constant-sheaf isomorphism. Its coefficient naturality
in every degree is `cohomologyPushforwardEquiv_naturality`, proved by right
naturality of that Ext equivalence and associativity of Ext composition.
`cohomologyPushforwardNatIso` packages exactly these equivalences as a natural
isomorphism from cohomology after pushforward to cohomology on `X`; its forward
component formula is `cohomologyPushforwardNatIso_hom_app`.

For an arbitrary short exact sequence `S` of abelian sheaves on `X`,
`cohomologyPushforwardEquiv_δ` identifies its actual connecting map with the
connecting map for `S` pushed forward along `e.hom`, in every pair of degrees
`n,m` with `n + 1 = m`. Exactness of this pushforward comes from the sheaf-category
equivalence. Mathlib's `Ext.mapExactFunctor_extClass` identifies the extension
class of the pushed sequence, right naturality of the adjunction equivalence
transports Ext composition with that class, and associativity moves the
constant-sheaf change past the composition.

`cohomologyPushforwardEquiv_equiv₀` proves that the existing equivalence is the
identity on global sections under the actual `Sheaf.H.equiv₀` identifications.
Inverse image of the top open is definitionally the top open, so these section
groups coincide. To prove the identity, write a degree-zero Ext class as
`Ext.mk₀ f`. The adjunction Ext equivalence then becomes its Hom equivalence.
The published constant-sheaf isomorphism is exactly uniqueness of the two left
adjoints to global sections. The unit identity for uniqueness of left adjoints
proves that precomposing with its inverse converts one Hom equivalence to the
other. Composition of adjunctions cancels the inverse-pushforward Hom
equivalence, giving the same global section. The section-to-cohomology formula
is `cohomologyPushforwardEquiv_equiv₀_symm`.

Provenance consists solely of the published `UnitSheafPushforward` definitions
and the pinned Mathlib exact-adjunction, Ext, sheaf-cohomology and adjunction
uniqueness APIs. No external theorem translation is asserted. The module
requires no compactness, scheme, cover, flasqueness or injectivity hypothesis.
Compatibility with the Čech comparison and the Picard-class pullback, deformation
theory, and representability of the fppf Picard sheaf remain separate obligations.
