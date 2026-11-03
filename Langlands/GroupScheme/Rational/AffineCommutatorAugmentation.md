# The actual commutator pullback on augmentation kernels

Worker 1228, using Worker 1282's affine commutator coordinate construction.
This internal construction combines `AffineCommutatorCoordinates` with
`AugmentedTensor`. It implements the tensor-kernel step of
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Lemma 3.3.4, printed pp.108–109 (PDF pp.134–135), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`.

First, the two generic identity-slice maps are identified with the tensor
algebra lifts used in the commutator-coordinate construction. Equality is
checked on pure tensors. The generic
`mapIncl_augmentationKernelProjection_eq` records the canonical preimage
provided by subtracting the scalar part in each factor: including the tensor
of the two kernel projections recovers every tensor whose two slices vanish.
Its proof factors the tensor map into the two single-factor projections and
uses the corresponding slice-subtraction formulas.

For arbitrary affine group schemes `G`, `H`, and `K` over a commutative ring,
and homomorphisms `i : H ⟶ G` and `j : K ⟶ G`, the standard slice equations
are obtained from the actual commutator pullback's existing slice equations.
`augmentationPullback i j` then maps the actual kernel of
`Lie.coordinateOrigin G` linearly into the tensor product of the actual
kernels of `Lie.coordinateOrigin H` and `Lie.coordinateOrigin K`. It applies
the two canonical kernel projections to `CommutatorCoordinates.pullback i j`.

`augmentationPullback_include` proves that composing this map with the
tensor of the kernel inclusions recovers the original coordinate pullback
on every augmentation element. The proof evaluates each slice equation
on that element; its augmentation is zero, so both slices vanish, and the
generic projection identity applies.
`pullback_mem_augmentationTensor` is the resulting range-membership
statement.

No field, smoothness, connectedness, or torus-action hypotheses are needed
for this construction. Injectivity of a pullback from an image closure,
the torus grading on coordinates, comparison with Lie weights, and generation
of a smooth connected invariant subgroup remain separate obligations.
This module does not prove the full all-test semigroup commutator bound.
