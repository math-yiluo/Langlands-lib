# Flatness of relative groups of multiplicative type

Worker 324.

This module provides the arbitrary-ring diagonalizable flatness instance and
imports the published flatness results for every group of multiplicative type over an
arbitrary scheme, using the Library's relative predicate. No smoothness,
connectedness, or torsion-free character-group hypothesis is imposed.

## Provenance

This is a derived geometry helper for the subgroup-preimage extension argument.
Its proof uses the actual coordinate algebra in
[`Torus.Diagonalizable`](Diagonalizable.md), the diagonalizing cover in
[`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), and
the existing fppf descent API in
[`FppfLocalAtTarget`](../../AlgebraicGeometry/Morphisms/FppfLocalAtTarget.md)
and [`FpqcFiniteDescent`](../../AlgebraicGeometry/Morphisms/FpqcFiniteDescent.md).
It introduces no additional literature assertion.

## Declarations and implemented proofs

For every commutative ring `R : CommRingCat.{u}` and abelian group
`Λ : Type u`, the instance
`Langlands.GroupScheme.Diagonalizable.flat` proves that the structure
morphism of `Diagonalizable.groupScheme R Λ` is flat. The scheme is the
spectrum of `AddMonoidAlgebra R Λ`. Mathlib's free-module instance for this
algebra supplies module flatness; `RingHom.flat_algebraMap_iff` and
`Flat.SpecMap_iff` identify this with flatness of the spectrum morphism.
Finite generation of `Λ` is unnecessary for this instance.

The following declarations are reused from
[`RelativeMultiplicativeTypeGeometry`](RelativeMultiplicativeTypeGeometry.md), in
`Langlands.GroupScheme.RelativeMultiplicativeType`:

- `flat_diagonalizable S Λ` proves flatness of `diagonalizable S Λ` for
  every scheme `S`. This group is obtained by base change from the integral
  model, so its structure morphism is the base change of a flat morphism.
- `IsDiagonalizable.flat` proves flatness of a group scheme over `S` from
  its isomorphism to a diagonalizable model. The proof writes its structure
  morphism as the composite of the underlying isomorphism and the model's
  flat structure morphism.
- `IsMultiplicativeType.flat` proves `Flat H.X.hom` from
  `IsMultiplicativeType H`. It unpacks the fppf diagonalizing cover, applies
  `IsDiagonalizable.flat` to each base change, and descends flatness by the
  existing local-at-target theorem for the fppf precoverage.

All declarations are proved in every universe `u`. The final two use the
published predicates, whose diagonalizable presentations have finitely
generated abelian character groups and can include torsion.
