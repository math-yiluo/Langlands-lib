# The Iwahori subgroup of an induced torus over the maximal unramified extension

Workers 1587 and 706. The theorem
`Langlands.Geometry.Building.inducedTorusIwahori` proves exactly
`Langlands.Geometry.Building.InducedTorusIwahoriStatement.{u}`, the case
over `K` of KP Lemma 2.5.18 described in the public statement's Markdown.
For every nonarchimedean local field `F`, put `K = UnramifiedClosure F`.
For every actual affine commutative group scheme `T` over `K` and every
finite Galois intermediate field `L` of `SeparableClosure F / K` splitting
`T`, the hypothesis `IsInducedTorus T` implies

```text
torusNormIwahori K L (intermediateValuation F L) T =
  characterValuationKernel (fixedFieldValuation F) T.toGrp.
```

The universe `u` is arbitrary, and either characteristic is permitted.
The theorem adds no premise to the public proposition.

Apply `inducedTorusWeilDecomposition` to the prescribed splitting field `L`.
It supplies intermediate fields `E i` inside that same `L` and an actual
isomorphism from `T` to the Weil restriction from their finite product.
Lift the `Fin n` index to `ULift.{u} (Fin n)` and transport the product
algebra by `AlgEquiv.piCongrLeft`. The isomorphism
`WeilGm.commCongrIso` then identifies the Weil restrictions. This places the
factor index in the universe required by the product-coordinate theorem.
An empty family is allowed throughout, so the rank-zero case is retained.

The inclusion from the norm Iwahori subgroup into the character kernel is
`torusNormIwahori_le_characterValuationKernel`, applied to the actual
`fixedFieldValuation F` and `intermediateValuation F L`. Galois invariance is supplied by `intermediateValuation_conjugate F L`,
and valuation compatibility by `intermediateValuation_extends_fixedField F L`.

For the reverse inclusion, map a point in the character kernel of `T`
through the isomorphism to the product Weil restriction `W`.
`map_characterValuationKernel_le` puts its image in the character kernel
of `W`. The equality
`weilProduct_torusNormIwahori_eq_characterValuationKernel F L E'`
places it in the norm Iwahori subgroup of `W`. Apply
`map_torusNormIwahori_le` to the inverse isomorphism. The composition law
for the underlying group homomorphisms and the isomorphism inverse law
identify the resulting point with the original point of `T`.

Provenance: this is an internal composition of the published structural
decomposition, finite-product bounded-norm calculation, and functoriality
of character kernels and rational norms. The product calculation uses
actual tensor-unit coordinates and the scalar unit-norm surjectivity
theorem over `K`. Worker 1587 assembled this final transport and the scalar
norm computations; Worker 706 supplied the character-kernel comparisons
used in that calculation. The imported structural decomposition was proved
separately by Workers 1548 and 1550.
