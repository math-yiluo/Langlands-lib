# Character twists of actual coefficient models

Author: Worker 31.

This module constructs the effect of a character twist on the actual
equivariant functionals and coefficient images from
`Langlands.Representation.Whittaker.Algebraic`. It reuses the published
`Langlands.twist` operation and `isSmooth_twist_iff`; it does not introduce a
second representation twist.

Let `R` be a commutative ring, `G` a group, `N` a subgroup, and
`θ : N →* Rˣ` a character. Let `χ : G →* Rˣ` be a character whose restriction
to `N` is one. The coefficient ring, group and representation module live
in independent universes `uR`, `uG` and `uV`. The module is an arbitrary
additive commutative group with an `R`-module structure.

`twistFunction χ` multiplies an actual function `f` pointwise by `χ(g)`.
Its inverse multiplies by `χ(g)⁻¹`; the unit identities prove both inverse
laws, and distributivity and commutativity prove linearity. The identity
`χ(ug)=χ(g)` for `u ∈ N` shows that both multipliers preserve the
`θ`-equivariant function space. Restriction gives `twistFunctionEquiv`.

`twistFunctional` and `untwistFunctional` retain the same underlying linear
functional. On `N` the original and twisted actions coincide, proving its
equivariance in each direction. Their inverse identities and linearity
are definitional, yielding `twistFunctionalEquiv`. The unchanged functional
also preserves nonvanishing, with no existence or uniqueness theorem assumed.

Linearity of the functional proves `twistFunction_coefficient`: the coefficient
of `v` for the twisted representation is exactly the original coefficient
multiplied by `χ(g)`. This formula restricts the multiplier to the actual
coefficient images, producing `twistModelLinearMap`. Injectivity follows from
the inverse function multiplier. For surjectivity, a vector witnessing
membership in the target coefficient image supplies its original coefficient
as a preimage.

The character law `χ(gs)=χ(g)χ(s)` proves that this image map intertwines
the scalar-twisted action on the original model with the ordinary
right-translation action on the model of the twisted representation.
`twistModelIntertwiner` bundles that compatibility, and its proved
bijectivity gives `twistModelEquiv`. These are actual representations on
actual coefficient images, including possibly the zero image.

For the smoothness construction only, put a topology on `G` and assume that
`χ` has open kernel. The published theorem `isSmooth_twist_iff` shows that a
smooth input representation remains smooth after twisting. The previously
proved intrinsic smoothness of coefficient images then yields
`twistModel_isSmooth`. No continuity of group operations, topology on the
representation module, local compactness, unitarity, irreducibility,
admissibility or finite-dimensionality is needed. Openness of the character
kernel is an explicit hypothesis, not inferred from bare continuity.

## Original source and derived content

The coefficient convention comes from Jacquet, Piatetski-Shapiro and Shalika,
*Rankin--Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367-464, section 0.3, printed page 377, and section 2.1, printed pages 385-386.
The function associated to a functional is `g ↦ ℓ(π(g)v)`, with right
translation as the representation action. Those original pages were read
directly. Registered source: `jpss-1983-rankin-selberg`; retained original:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

This pair is derived algebraic infrastructure. Substituting the published
scalar-twisted action into that coefficient formula gives the multiplier
`χ(g)`, and the proofs above construct its functional and image interfaces.
These general commutative-ring results are not additional claims quoted from
JPSS. The published twist definition documents its own scalar-twist source
convention. The GL determinant specialization is a separate consumer:
it must prove that the determinant character is trivial on the actual
upper-unipotent subgroup.

The only project imports are
`Langlands.Representation.Whittaker.Algebraic` and
`Langlands.Representation.Twist.SmoothProof`, both published. Their implementations
are reused by import, not republished as part of this contribution. No genericity
existence, multiplicity one, or local-factor transformation law is supplied.
The intrinsic obligations of the functionals, image maps, representation
equivalence and smoothness construction are proved in this pair. Independent
semantic review accepted this construction contribution.

The complete module compiled without errors or warnings with Lean 4.34.0 and
the pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
This native result is development evidence, separate from independent checking
and review.
