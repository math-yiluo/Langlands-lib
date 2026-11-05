# Splitting a zero coordinate from an additive polynomial kernel

This internal construction supplies the actual product isomorphism for the
kernel of an additive polynomial row with a zero coordinate. It combines the
universal properties of products and kernels with the natural vector-group
coordinates already in the Library. It is a prerequisite for iterating the
existing polynomial coordinate reduction.

`Langlands.GroupScheme.kernelSndIso G f` identifies the kernel of the second
projection `G ⊗ H ⟶ H` followed by `f : H ⟶ L` with `G ⊗ kernel f`.
It works over every scheme base and requires no commutativity of the group
schemes. Its forward map records the first ambient component and lifts the
second ambient component into `kernel f`. Its inverse takes the product of
the identity of `G` and the kernel inclusion and lifts this into the kernel
of the composite. The inverse laws follow by the product and pullback
projection identities. The three following compatibility formulas give the
first projection, the second projection followed by its kernel inclusion,
and the inverse followed by the composite-kernel inclusion.

`VectorGroup.splitCoordinates j` separates a tuple into the constant
one-coordinate tuple with value at `j` and the remaining tuple indexed by
`j.succAbove`. Its inverse uses `Fin.insertNth`. The construction only
requires an additive monoid of coordinate values.
`VectorGroup.splitPoints R j T` transports this equivalence through the
actual vector-group coordinate equivalences and the product point equivalence.
The two coordinate formulas state its values on both product projections.
They also prove compatibility with arbitrary maps between relative test
schemes: all coordinates are pulled back by the same map of global functions.
The existing group-valued Yoneda construction then gives
`VectorGroup.splitIso R j`, an actual group-scheme isomorphism
`V_(n+1) ≅ V_1 ⊗ V_n` over any commutative ring `R`.

For an additive row `f : Fin (n+1) → k[X]` over any field and a coordinate
`j` with `f j = 0`, `splitIso_hom_snd_comp_polynomialRow` proves that this
isomorphism followed by the second projection and the reduced row
`i ↦ f (j.succAbove i)` equals the original row as an actual homomorphism.
The proof evaluates on every relative scheme test and uses
`Fin.sum_univ_succAbove` to remove the vanishing term. Thus it also covers
nonreduced test schemes and finite fields.

`polynomialKernelZeroCoordinateIso` restricts this ambient isomorphism to
the actual kernels using `kernelCoordinateIso`, then composes with
`kernelSndIso`. Its result is
`kernel(row f) ≅ V_1 ⊗ kernel(row (f ∘ j.succAbove))`.
`exists_polynomialKernelAdditiveFactor_of_zeroCoordinate` first transports
through any ambient coordinate reduction supplied by
`HasPolynomialKernelZeroCoordinate` and then applies this isomorphism.
Finally,
`exists_polynomialKernelAdditiveFactor_of_not_hasConstantAffineLineMaps`
uses the existing coordinate-reduction theorem to obtain a product
decomposition with a polynomial kernel in one fewer variables whenever the
original polynomial kernel fails actual affine-line constancy.

No field infinitude, perfection, characteristic restriction or assumed
coordinate presentation of an arbitrary unipotent group is used. This unit
constructs a single additive direct factor of an explicit polynomial kernel;
iteration to a constant-map complement and the arbitrary-group woundness
criterion remain separate obligations.
