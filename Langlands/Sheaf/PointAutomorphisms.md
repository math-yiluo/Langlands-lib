# Automorphisms of a site point and smooth module fibers

This internal categorical construction supplies a local action on the actual
fiber functor of a Mathlib site point. It is a prerequisite toward an analytic
local-stalk comparison, rather than an identification with any absolute Galois
group.

For a site point `Φ`, `AutGroup Φ` is the automorphism group of its actual
Type-valued functor `Φ.fiber`. The topology is induced by its action on the
discrete disjoint union of all sets `Φ.fiber.obj U`, with the function space
carrying the product topology. This is pointwise convergence on individual
fiber elements. In particular it does not require fibers to be finite.

Multiplication is continuous because evaluation of a permutation at a variable
point is continuous when that point is discrete. For inversion, fixing the
image of the inverse image of a particular point forces the inverse image to
stay fixed. Thus inversion is continuous as well. Each fiber-element stabilizer
is an open subgroup, as the inverse image of an open singleton under evaluation.
The evaluation embedding is injective, so the topology is Hausdorff.

`presheafFiberEnd` uses the universal property of the actual colimit defining
`Φ.presheafFiber`: an automorphism sends the germ indexed by `(U,x)` to that
indexed by `(U,σ(x))`. Naturality of the automorphism ensures compatibility
with restriction maps.

For a commutative ring `R : Type w`, module carriers in `Type w`, and a point
with fibers in `Type w`, `fiberRepresentation` is the resulting algebraic
representation. Its multiplication law is proved by checking the canonical
maps into the colimit. The order agrees with the categorical automorphism
convention: `σ * τ` acts first by `τ`, then by `σ`.

When the site category is locally small in `w`, forgetting modules to sets
preserves the filtered colimit. Every stalk element is therefore represented
by an actual section and a fiber element `(U,x)`. The open stabilizer of `x`
fixes its germ. This proves `fiberRepresentation_isSmooth` for every module
presheaf, with no sheaf or injectivity assumption.

Naturality of the colimit action gives `fiberIntertwiningMap` and the functor
`presheafSmoothFiber`. Composing with the actual sheaf-to-presheaf functor
gives `sheafSmoothFiber`. The two forgetful isomorphisms
`presheafSmoothFiberForgetIso` and `sheafSmoothFiberForgetIso` recover the
original Mathlib fiber functors, with identity components. Object, morphism,
point-fiber, and module universes are explicit; only the coefficient and
module-carrier universe is shared with the point-fiber universe.

The construction is derived directly from the definitions and colimit universal
properties in Mathlib's `CategoryTheory.Sites.Point.Basic`; no analytic
comparison or cohomological vanishing result is an input. An identification
with analytic absolute-Galois stalks and compact-support acyclicity remain
separate obligations.
