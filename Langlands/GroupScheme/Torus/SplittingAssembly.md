# Hopf-coordinate comparisons for torus splitting

Author: Worker 1337.

This module constructs the comparison between scalar-extended actual
coordinates and the base-changed group scheme, and proves the resulting
group-like spanning and affineness lemmas. A conditional assembly
theorem records the remaining separably closed proof interfaces explicitly. The module does
not prove the unconditional finite Galois splitting proposition.

`span_of_coalgEquiv` maps a spanning family through a coalgebra equivalence.
The equivalence is surjective and sends group-like elements to group-like
elements, so its image spans the target. The coalgebra, module, and field
types have independent universes.

`span_of_hopfSpecIso` uses Mathlib's fully faithful Hopf spectrum functor.
The inverse image of a group-scheme isomorphism gives a Hopf-algebra
isomorphism in the opposite direction, and its underlying coalgebra
equivalence transports group-like spanning.

`span_of_isSplit_hopfSpec` uses the published
`Diagonalizable.hopfSpecIso` to compare the standard additive group-algebra
Hopf spectrum with the actual diagonalizable group scheme. For a split
torus on a finite type `I`, the published `Diagonalizable.splitIso`
identifies its diagonalizable presentation with the group algebra of
`I → ℤ`. Mathlib proves that this algebra is spanned by group-like
monomials. The preceding transport gives spanning for the original Hopf
algebra. The empty finite type, and therefore rank zero, is included.

`scalarExtensionCoordinatesIso` applies to commutative rings `k` and `K`
in a common arbitrary universe, an algebra `k → K`, and an actual affine
group scheme `T` over `Spec k`. It composes the inverse of the published
`HopfCoordinates.baseChangeSpecIso` with the base change of
`AffineCoordinates.hopfSpecIso T`. The result is an isomorphism of actual
group schemes from the Hopf spectrum of
`K ⊗[k] AffineCoordinates.hopfAlgebra T` to the base change of `T`.
It preserves the group law, identity, and inverse; no field or flatness
assumption is needed for this construction.

`span_scalarExtension_of_isSplit` specializes this comparison to fields.
Splitting of the actual base-changed group scheme therefore gives group-like
spanning of its scalar-extended coordinate Hopf algebra.

`isAffine_of_isTorus` applies the published theorem
`Langlands.AlgebraicGeometry.fieldExtensionAffineDescent` to the arbitrary
splitting field supplied by `IsTorus`. Affineness of the split base change
follows from `IsSplitTorus.isAffineHom`. Thus every actual field torus in
the existing sense is affine, with no restriction on its splitting witness.

`isSplit_of_isSepClosed_of_prerequisites` first obtains this affine instance,
then forms the actual coordinate Hopf algebra. The original splitting field
supplies scalar-extension spanning by the preceding lemma. An explicitly
supplied proof of the published pure-coalgebra spanning-descent proposition
gives spanning over the separably closed ground field. The published theorem
`IsTorus.isSplitTorus_of_groupLike_span` then produces `IsSplitTorus T` from
affineness, `IsTorus T`, and coordinate spanning. Only the pure-coalgebra
descent input remains an explicit proof obligation in this theorem.

All implemented steps are internal consequences of the imported Library and
Mathlib constructions and the explicit hypotheses of the conditional
theorem. No new source proposition is transcribed. The original arbitrary
characteristic, imperfect-field, and rank-zero scope is retained. The
pure-coalgebra descent proof and finite-stage descent must be supplied before
the unconditional target can be proved.
