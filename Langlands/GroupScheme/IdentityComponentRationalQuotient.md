# Rational points modulo the identity-component subgroup

This derived construction forms the actual group
`RationalComponentQuotient H = H(k) / H⁰(k)` for a smooth affine group scheme
`H : GroupScheme (Spec k)` over any field `k`. Here `H(k)` is the existing group
of rational sections in `Over (Spec k)`, and `H⁰(k)` means the subgroup of sections
factoring through the published inclusion `identityComponentι H`. The quotient
projection has exactly that kernel. The construction also supplies an embedding
of the quotient into the connected components of the underlying scheme and proves
the quotient finite.

The field, group scheme and test schemes share an arbitrary universe `u`.
Smoothness and affineness are the only geometric hypotheses. There is no
assumption on characteristic, perfection, connectedness, reductivity or the
number of rational points. `pointComponent` and its translation evaluation law
are defined without smoothness or affineness. All subsequent declarations use
both hypotheses.

## Construction and intrinsic laws

`rationalIdentitySubgroup H` is the rational-section specialization of
`SubgroupFunctor.range (identityComponentι H)`. Its normality follows directly
from the published all-test normality of that range.

`pointComponent H x` is the connected-component class of the scheme point
`x.left (basePoint k)`. The identity-component inclusion is an open immersion
whose range is precisely the connected component of the identity. A section
factoring through it therefore has the identity component class. Conversely,
if the class is that of the identity, every point in the section's range lies
in that open subscheme: `Spec k` has just one point. The published general
open-immersion lift `FiniteEtaleImage.liftOver` then constructs a section of
`H⁰` with the given image. This proves `mem_rationalIdentitySubgroup_iff`.

Translation by `x⁻¹` is a scheme automorphism and induces the published
permutation `translationComponents H x⁻¹`. Its injectivity and evaluation law
show that two rational sections `x` and `y` have the same component class if
and only if `x⁻¹ * y` belongs to `rationalIdentitySubgroup H`. This is
`pointComponent_eq_iff`, precisely the relation used by Mathlib's group quotient.

`rationalComponentProjection` is the canonical surjective group homomorphism.
`ker_rationalComponentProjection` identifies its kernel with the subgroup
defined above. `rationalComponentEmbedding` descends `pointComponent` to the
quotient, and the same relation equivalence proves it injective.
`rationalComponentEmbedding_projection` computes it on representatives.
The imported `finite_connectedComponents` proves that a smooth affine field
group has only finitely many scheme connected components. The embedding
therefore gives the instance `finite_rationalComponentQuotient`.

For any target group `M` and homomorphism `f : H(k) →* M` killing
`rationalIdentitySubgroup H`, `rationalComponentLift` is its factor through
the quotient. `rationalComponentLift_projection` gives the factorization
equation, and `rationalComponentLift_unique` gives uniqueness. These are the
ordinary group-quotient universal property.

## Provenance and scope

The provenance is internal and derived. This file composes the published
`IdentityComponent`, `IdentityComponentPowers`, `SubgroupFunctor` and
`FiniteEtaleImage` constructions with Mathlib's normal subgroup quotient.
The membership, component comparison, embedding, finiteness and lift laws are
intrinsic verification of this new quotient construction; no additional
literature theorem is invoked.

This is a quotient of rational-point groups. It constructs no component group
scheme or sheaf quotient and makes no comparison with rational points of such
a quotient. The embedding targets the connected components of the underlying
`k`-scheme and is not claimed surjective: a component need not have a rational
point. No topology on rational points, cyclic-closure smoothness or
torus/additive factorization is asserted.
