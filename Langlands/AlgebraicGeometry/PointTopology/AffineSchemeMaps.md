# Global-section maps and affine presentation comparisons

Author: Worker 105.

This is a derived host comparison for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Proposition 2.1 and its
proof, printed pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For an actual morphism of affine schemes over `Spec R`,
`affineCoordinatePullback` is its actual pullback on global sections.
The algebra structures are those of `AffineScheme`: they retain each
scheme's specified structure morphism to the base. Their compatibility
is proved using naturality of Mathlib's canonical affine isomorphism
and faithfulness of the spectrum functor.

`affineSchemePointEquiv_spec` identifies the spectrum of the algebra
map associated with a relative point with that actual scheme point
followed by the canonical affine isomorphism.
`affineSchemePointEquiv_natural` proves that postcomposition of actual
relative scheme points agrees with precomposition by the global-section
algebra pullback. This supplies the algebraic bridge needed to transfer
the evaluation topology's mapping properties to arbitrary affine
scheme objects. Pullback respects identities and composition, so an
actual isomorphism of schemes over the base gives
`affineCoordinateAlgEquiv`, an isomorphism of their coordinate algebras
in the contravariant direction.

`affineSchemePointIsoHomeomorph` combines that coordinate-algebra
isomorphism with the evaluation-topology comparison. Its application
formula proves that the map is postcomposition of the original relative
scheme point with the supplied scheme isomorphism.

For `Spec A`, `spectrumCoordinateMap` identifies the actual base map into
global sections with the composite through the inverse of Mathlib's
`Scheme.ΓSpecIso`. Consequently `spectrumCoordinateAlgEquiv` is the
global-sections ring isomorphism as an isomorphism of the specified
`R`-algebras. `affineSchemePointEquiv_spectrum` proves agreement of
the two coordinate-point descriptions under that isomorphism.
`spectrumRingPointHomeomorph` therefore compares the global-section
topology on `RingPoint` with the previously constructed topology on
`SpecPoint`; its application formula proves that the underlying
scheme morphism is unchanged.

Finally, `affinePresentationPointHomeomorph` applies to any isomorphism
over `Spec R` from the given affine scheme to `Spec A`. Its underlying
map is postcomposition with precisely that isomorphism, so this is a
proved comparison for arbitrary affine spectrum presentations.

All algebraic comparisons require only commutative rings and the stated
base algebra structures. The homeomorphisms additionally require only
a topology on the value ring `S`; no continuity of ring operations,
finite type or separation is assumed. Only `S` has a topology.

This unit does not assert the source's general scheme-morphism
continuity or closed-immersion mapping properties, finite-coordinate
embedding theorem, nonaffine gluing or axiomatic uniqueness.
