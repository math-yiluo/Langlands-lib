# Nonconstant restrictions of affine roots

This internal affine-geometric construction uses the published
`AffineRootSystem` definitions and Mathlib affine maps. It introduces no
assertion from the original literature. Its purpose is to isolate a
geometric step needed in scalar-extension descent: specialness and the
vertex property of a point in the image of an apartment map.

For an arbitrary real affine map `f : A →ᵃ[ℝ] B` and an arrangement `Ψ` of
affine functionals on `B`, `restrictedRoots f Ψ` consists exactly of the
composites `ψ.comp f` with `ψ ∈ Ψ` whose derivatives are nonzero. The
translation spaces and affine spaces have independent universes.

`facetRel_restrictedRoots_iff` proves that two source points have the same
signs for the restricted roots exactly when their images have the same
signs for all ambient roots. An ambient root discarded in the restriction
has constant composite, so it imposes no additional condition.
Consequently, `facet_restrictedRoots_eq_preimage` identifies every source
facet with the full inverse image of the corresponding ambient facet. If
`f` is injective and `f x` is an ambient vertex, the inverse image of its
singleton facet is `{x}`. This proves
`isVertex_restrictedRoots_of_isVertex`.

`isSpecialPoint_restrictedRoots_of_isSpecialPoint` assumes that every
ambient root has nonzero derivative. For a source root, choose its
ambient representative. Specialness of `f x` gives an ambient root that
vanishes there and has parallel hyperplane. The published kernel
characterization of parallel hyperplanes identifies their derivative
kernels. Taking preimages along the linear part of `f` identifies the
restricted kernels. The chosen vanishing root therefore still has a
nonzero derivative after restriction, so it belongs to `restrictedRoots`
and vanishes at `x`. The same kernel characterization proves specialness.
This proof does not require injectivity or surjectivity of `f`.

`isSpecialPoint_of_restrictedRoots_eq` applies the result to another
supplied arrangement when it is exactly the nonconstant restriction.
No assertion is made that the restricted arrangement satisfies the
affine-root-system axioms. No actual building bundles, scalar-extension
apartment map, identity of their root arrangements, special-point
existence, or membership of a canonical-model point in the apartment
image is constructed here. Those remain separate obligations for
`IntegralModel.BuildingComparisonStatement`.
