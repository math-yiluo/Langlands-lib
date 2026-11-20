# Splitting invertible functions on a product of irreducible varieties

`Langlands.GroupScheme.unitsProductDecomposition` proves the published
`Langlands.GroupScheme.UnitsProductDecompositionStatement.{u}` for every
universe `u`. For irreducible, reduced, separated schemes of finite type
over an algebraically closed field, every morphism from their product to
the multiplicative group is a product of pullbacks of morphisms from the
two factors.

## Implemented proof

The proof specializes `Langlands.Algebra.rosenlichtTensorUnits` to universes
`{u,u,u}`. That theorem factors each unit of the tensor product of two
finite-type domains over an algebraically closed field as a pure tensor
of units.

`Langlands.GroupScheme.UnitsProduct.affine_splitting_of_domain_tensor_units`
transports this result through the coordinate-ring equivalence for an
affine product and the equivalence between units of global sections and
morphisms to the multiplicative group. The affine integral schemes of
finite type supply the required finite-type domain coordinate rings.

`Langlands.GroupScheme.UnitsProduct.geometric_reduction` chooses pointed
nonempty affine charts and splits the restriction to their product. The
restrictions to the two axes through the chosen points, with a correction
by the inverse of the value at the joint point, give the global factors.
The product of the resulting pullbacks agrees with the original morphism
on the dense open product of the charts. Reducedness of the source and
separatedness of the multiplicative group extend the equality to the
whole product.

The direct imports are
`Langlands.GroupScheme.Torus.UnitsProductGeometricReduction`,
`Langlands.GroupScheme.Torus.UnitsProductAffineReduction`, and
`Langlands.Algebra.RosenlichtTensorUnits`. Their paired Markdown describes
the component proofs.

## Source

James S. Milne, *Algebraic Groups* (2017), Proposition 12.48 and its proof,
printed pages 246–247 (PDF pages 262–263), registered source
`milne-2017-algebraic-groups`.
