# Geometric eigenspaces for actual conjugation

This is an internal supporting construction by Worker 1296. It derives an
eigenspace decomposition for the scalar extension of the actual coordinate
conjugation derivation. Its inputs are the actual representation coefficients
and intertwiner in `Lie.ConjugationSemisimple` and the scalar extension of
derivations in `CommutativeAlgebra.DerivationBaseChange`. It asserts no additional
external structural theorem. Smoothness descent and the Cartan-generation
conclusion are applications outside this module.

Let `k : Type u` be any field, let `G` be an actual affine group scheme over
`Spec k`, and put `K = AlgebraicClosure k` and `B = coordinateAlgebra G`.
No smoothness, connectedness, finite-type, infinitude or perfection hypothesis
is imposed here. Finite matrix indices lie in `Type` and may be empty.

`IsSemisimpleElement.isGeometricallySemisimple_tangentMatrix` extends the
representation test from `Fin N` to every finite indexing type. The proof
reindexes an actual representation along `Fintype.equivFin`, uses the actual
tangent reindexing identity, and transports semisimplicity over `K` through
the resulting linear equivalence. This lemma does not require affineness.

For an actual finite representation `ρ`, write `M(i,j)` for its universal
matrix coefficients. `geometricCoefficientLinearMap` is the `K`-linear map
from functions on pairs of indices to `K ⊗[k] B` given by

```text
v ↦ Σ(i,j) v(i,j) • (1 ⊗ M(i,j)).
```

`geometricCoefficientLinearMap_intertwines` proves that this map intertwines
the negative tangent matrix of the actual dual-tensor representation
`ρ.dual.tensor ρ`, with entries extended to `K`, and the extended conjugation
derivation `D_K = baseChange K (conjugationDerivation G X)`. The proof checks
the standard coordinate basis, applies the original coefficient intertwiner,
and moves scalars and finite sums through a pure tensor. In particular, the
sign and the pair-index convention are inherited from the actual
conjugation calculation rather than from an independent adjoint convention.

`geometricCoefficientLinearMap_algebraMap` identifies the image of a
coefficient vector extended entrywise from `k` with `1 ⊗` its original image.
It follows directly by distributing the tensor over the coefficient sum.
`geometricCoefficientLinearMap_range_invariant` then obtains invariance
under `D_K` from the intertwining identity.

For a representation-semisimple Lie element `X`,
`IsSemisimpleElement.isSemisimple_geometricCoefficient_range` proves
semisimplicity of the restriction of `D_K` to this range. The source
endomorphism is semisimple by the geometric test applied to the actual
dual-tensor representation and preservation under negation. The coefficient
map onto its range is a surjective intertwiner.

`IsSemisimpleElement.geometricCoefficient_range_le_eigenspaces` places each
such range in the supremum of the eigenspaces of `D_K`. The range is finite
dimensional, and `K` is algebraically closed, so its restricted semisimple
operator has spanning eigenspaces. Mapping these eigenspaces through the
submodule inclusion gives eigenspaces of the ambient operator.

Finally,
`IsSemisimpleElement.hasEigenDecomposition_conjugation_baseChange` proves
the exact `HasEigenDecomposition D_K.toLinearMap` predicate: the supremum
of all its eigenspaces is the whole tensor product. For each original
coordinate `c`, finite coefficient-span coverage supplies an actual
representation whose coefficient range contains `c`. The scalar-extension
identity places `1 ⊗ c`, and hence every `s ⊗ c`, in the geometric coefficient
range. The preceding range inclusion places each pure tensor in the
eigenspace supremum. Tensor induction and closure under addition finish the
proof, including arbitrary elements of the tensor product.
