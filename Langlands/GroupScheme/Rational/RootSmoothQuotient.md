# Actual root maps induced by smooth quotient homomorphisms

This internal construction starts with a homomorphism `q : H ⟶ G`, a
commutative group scheme `S` mapped into `H` by `i`, a character `a`, and
actual all-test representatives `j : U ⟶ H` and `l : V ⟶ G` of the
intrinsic root functors for `i` and `i ≫ q`.

Over an arbitrary base scheme, `range_comp_le` proves that `j ≫ q`
lands in the target root functor. It applies the published preservation
of character-orbit extensions under homomorphisms to every test point.
`rootMap` is the canonical factorization through `l`, constructed using
the represented subgroup's factorization property. `rootMap_comp`
states the exact ambient composite identity.

Over a field, assume `H` and `G` are smooth affine, `S` is split, and
`a` is nonzero. No connectedness, reductivity, maximality or occurrence
of `a` as an actual root is required. If the original scheme map `q` is
smooth and surjective, `rootMap_smooth_surjective` proves that the
canonical map `U ⟶ V` is also smooth and surjective as a scheme map.
This does not assert surjectivity on rational points.

The proof identifies both full root functors with the first positive
cyclic semigroup functors using the published
`weightFiltration_one_eq_subgroup`. The two conjugation actions
intertwine under `q`. The published `semigroupSmoothQuotient` gives a
smooth surjection between the same representatives, and cancellation of
the target's monomorphic inclusion identifies it with `rootMap`.

`smooth_kernel_comp` concerns the full scheme-theoretic kernel of the
original composite `j ≫ q`. Smoothness of `rootMap` makes its kernel
smooth by pullback along the unit. Postcomposition with the monomorphic
root inclusion `l` preserves the entire kernel functor. The published
represented-kernel transport theorem therefore transfers smoothness to
the kernel of `j ≫ q`.

With the source representative affine, `lie_range_comp` identifies the
actual differential range of `j ≫ q` with the full positive cyclic
weight span for the torus map `i ≫ q`. This part needs smoothness of
`q`, but not surjectivity of its scheme map. The proof first identifies
the differential range of `j` with the intrinsic root tangent submodule,
then uses the exact root Lie-image theorem and the published
surjectivity on semigroup weight spans under a smooth equivariant map.
Differentiation respects the actual composite.

All declarations are at arbitrary universe `u`. The provenance is an
internal consequence of the published intrinsic root functor,
cyclic-semigroup comparison, smooth semigroup quotient, smooth tangent
weight and represented-kernel transport results. This unit supplies a
general geometric tool for the quotient of an integral root model's
special fibre. It does not identify which quotient roots survive a
change of facet, or prove a facet sign formula.
