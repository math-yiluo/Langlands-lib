# Actual unirational parametrizations and rational density

Worker 1574. This is an internal interface for using an actual affine-space
parametrization in a rational-density argument.

`IsUnirational k X` requires a finite indexing type `ι`, a nonempty open
subscheme `U` of the actual affine space `𝔸(ι; Spec k)`, and an actual
ground-field morphism `U → X` with dense underlying image. Thus the
parametrization is a scheme morphism over `Spec k`; it is not an arbitrary map
of points or a density certificate without a parametrization. The definition
includes nonemptiness of `U` and does not require a chosen rational point or
a separability condition on the morphism.

`IsUnirational.hasDenseRationalPoints` proves density of actual ground-field
rational sections when `k` is infinite. It applies the published affine-space
density theorem, restricts that density to `U`, and then maps the dense set
along the supplied dominant morphism. This proof does not need the finiteness
or nonemptiness fields of the parametrization beyond their role in the
definition.

All three proof inputs are imported from
`Langlands.AlgebraicGeometry.PointTopology.AffineDensity`:
`hasDenseRationalPoints_affineSpace`, `hasDenseRationalPoints_open`, and
`hasDenseRationalPoints_of_denseRange`. The internal definition packages the
usual affine-open dominant-parametrization condition for use by a separate
construction of the variety of maximal tori. This module asserts no
unirationality result for that variety or for a general group scheme.
