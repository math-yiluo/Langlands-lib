# Ampleness on finite disjoint unions

This internal supporting module works in every universe `u` with actual
`LineBundle` objects and the existing section-generation-locus definition of
`LineBundle.IsAmple`.

`FiniteCoproduct.isClosedImmersion_ι` proves that each component inclusion
is a closed immersion for an index type in universe `u`, without requiring
the index to be finite. Its complement is the union of the other component
images, which are open. This adapts the argument of
`Langlands.AlgebraicGeometry.isClosedImmersion_sigma_ι` to the larger
index universe, and removes its unused finiteness hypothesis.

For any family of scheme morphisms `f i : X i ⟶ Y i`,
`FiniteCoproduct.isPullback_component` proves that the square consisting of
`f i`, the two component inclusions and the induced map of coproducts is
cartesian. The component inclusions are open immersions. The preimage of a
target component is exactly the source component: every point comes from a
source component, and `sigmaι_eq_iff` detects its index.
`componentPullbackIso` packages the resulting isomorphism to the actual
categorical pullback.

If the index type is finite and the total scheme `∐ X` is compact and
quasi-separated, `LineBundle.isAmple_of_finite_coproduct` proves ampleness
of a given line bundle from ampleness of its actual component pullbacks.
The proof maps each `X i` to its affine hull `Spec Γ(X i, ⊤)`. The finite
coproduct of these affine hulls is affine. The cartesian component squares
identify the pullbacks of the given bundle to its component cover with
the prescribed restrictions. The established ampleness theorem for open
covers of an affine base then gives the conclusion.

`LineBundle.isAmple_finite_coproduct_iff` adds the converse, using affine
pullback along a component inclusion. Such an inclusion is affine because
its image is also closed in the coproduct. The hypotheses of compactness
and quasi-separatedness concern the total scheme; in the parabolic
application they follow from properness over an affine scheme. No
nonempty-index hypothesis is made. In particular, the forward construction
also handles the empty coproduct, where the local condition is vacuous.

These are derived scheme and line-bundle comparison results supporting the
finite parabolic determinant ampleness task. They assert no geometric
positivity for any parabolic determinant. Their provenance is the existing
scheme coproduct, open-immersion, actual pullback and affine-base ampleness
APIs, with no additional literature assertion.
