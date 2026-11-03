# Integral weights in the full-kernel identity component

This internal supporting unit works over an arbitrary field in universe `u`.
Let `T` be a split torus, `i : T → G` a homomorphism into an affine group of
locally finite type, and `j : C → G` a smooth affine representative of the
all-test centralizer of the full scheme-theoretic kernel of a character `a`.
The character need not be nonzero or primitive. The ambient group need not be
reductive.

Differentiating composition gives composition of the actual dual-number kernel
maps. The actual inclusion `C⁰ → C` is an open immersion, hence smooth.
The published smooth-differential lifting theorem therefore makes its
differential surjective over every coefficient algebra. Consequently
`IdentityComponent.range_targetMapLinear_comp` identifies the ambient
differential ranges of `C⁰ → C → G` and `C → G`.

The full-kernel invariant computation identifies the Lie image of `C → G` with
`integralWeightSpan i a`, the sum of all integer-multiple weight spaces,
including zero. The local Lie-kernel instances explicitly reuse the published
commutative group and module structures; they add no hypothesis. Uniqueness of
exact Lie images and the preceding range equality give `kernelCentralizerIdentity_hasLieImage` for the actual component.

The actual lifted torus in `C⁰` acts by conjugation, compatibly with the ambient
inclusion. The published tangent-weight transport theorem identifies the image
of each intrinsic component weight space with the intersection of the ambient
weight space and the full integral weight span.
`semigroupWeightSpan_zmultiples` identifies that span with the semigroup span of
the full additive subgroup `ℤ a`. For each character in this subgroup, its
weight space is a summand of the integral span, so the preceding intersection
is the entire ambient weight space. Injectivity of the actual differential
then gives `kernelCentralizerIdentityWeightSpaceEquiv`. Its forward map is
exactly `Lie.targetMapLinear (identityComponentι C ≫ j) k`, as the companion
coercion formula records. This includes the zero character.

Independence of split-torus weights identifies the support exactly.

Thus `relativeRoots_kernelCentralizerIdentityTorus` states that the component's
intrinsic relative roots are the ambient relative roots intersected with
`ℤ a`, as subsets of the same original character lattice. In particular an
ambient root `a` remains a relative root in the component.

These are internal consequences of the published full-kernel invariant,
smooth differential, identity-component, and weight-transport constructions.
No reduced kernel or restricted test schemes are used. This unit does not
assert centralizer reductivity or construct a rational normalizing
representative, integral coroot, or reflection.
