# Adjoint coefficients for a homomorphism

This internal construction packages an actual coefficient representation for
homomorphism deformation. Let `R` be a commutative ring, `G` a smooth affine
group scheme over `Spec R`, `H` any group scheme over `Spec R`, and `f : H ⟶ G`
an actual group-scheme homomorphism. For any `R`-module `N`,
`homomorphismCoefficients f N` is a natural regular representation of `H` on
`Additive (lieKernel G R) ⊗[R] N`.

The construction uses the actual adjoint representation of `G` from
`DifferentialRepresentation`, tensors its action with the trivial action on
`N` by `TensorCoefficients`, and restricts along `f` using `SourceTransport`.
`homomorphismCoefficients_action` identifies the action on a tensor point with
the adjoint action of `f(h)` on its Lie factor, leaving its `N` factor fixed.
The formula follows from the tensor action formula.

There are no conditions on `N` beyond its module structure, and no affineness
or smoothness assumption on `H`. The target `G` is assumed smooth and affine
here. This construction does not identify this module representation with
conjugation on an arbitrary square-zero reduction kernel, nor does it prove
the infinitesimal lifting statement. The provenance is the composition of the
three internal constructions named above; no additional source assertion is
used.
