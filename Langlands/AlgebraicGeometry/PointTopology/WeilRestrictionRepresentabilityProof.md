# Affine Weil restriction on all test schemes

The theorem `weilRestrictionRepresentabilityProperties` proves
`WeilRestrictionRepresentabilityProperties`, the separate statement of the
universal property implicit in Conrad's Example 2.4, printed page 3 of *Weil
and Grothendieck approaches to adelic points* (December 31, 2011). The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proof was written by Worker 105.

The rings `A` and `B` are arbitrary commutative rings with an `A`-algebra
structure on `B`, finite and projective as an `A`-module. The scheme `X` over
`Spec B` is affine and its structure morphism is locally of finite type.
The test scheme `T` over `Spec A` is arbitrary. The conclusion concerns the
existing canonical map obtained by pulling back a morphism to the constructed
Weil restriction and composing with its universal counit. It imposes no
affineness, finiteness, separation or quasi-separatedness condition on `T`,
and no topological, faithful-module or finite-presentation premise.

The implemented proof first transfers the actual relative-spectrum
equivalence `affineWeilRestrictionAffineTestEquiv` through the canonical
isomorphism `affineSchemeOverIso` of an affine test scheme with the spectrum
of its global sections. Naturality (`affineWeilRestrictionComparison_natural`)
identifies this transferred map with the canonical comparison; this is
`affineWeilRestrictionComparison_bijective_of_isAffine`. For a general test
scheme, equality of two preimages is tested on its affine open cover, proving
injectivity (`affineWeilRestrictionComparison_injective`).

For surjectivity, restrict a given base-changed morphism to the base changes
of the affine members of the test scheme's open cover. Affine bijectivity
provides local preimages. Their restrictions to pairwise overlaps have the
same canonical comparison by naturality, so general injectivity makes them
equal. Mathlib's open-cover gluing constructs the global morphism. Its
structure-map equation follows from the local equations and open-cover
extensionality. The canonical comparison equals the requested morphism after
restriction to the base-changed open cover; a second application of
open-cover extensionality proves the global equality
(`affineWeilRestrictionComparison_surjective`).

The proof uses the algebraic construction's finite projective coefficient
algebra generality, including nonfaithful algebras, with no assertion about a
coefficient embedding. The topology and the remaining whole-paper claims
are separate obligations.
