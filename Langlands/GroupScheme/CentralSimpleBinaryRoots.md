# Actual binary elementary maps in the canonical reduced-norm-one group

This is an internal construction from the published finite-algebra unit scheme, its canonical reduced-norm character, the matrix/tensor point equivalence, and the binary elementary maps. Throughout, `k D : Type u`, `k` is a field, and `D` is a finite-dimensional central simple `k`-algebra with a possibly noncommutative ring structure. The universe and characteristic are unrestricted.

## Actual target and norm comparison

`matrixBasis` is `Module.finBasis k (Matrix (Fin 2) (Fin 2) D)`. `groupScheme` is the actual canonical kernel `CentralSimpleUnits.normOne k (Matrix (Fin 2) (Fin 2) D)`, with its existing group structure and inclusion `normOneι`. The instance `inclusion_mono` exposes the monomorphism of its underlying relative scheme morphism, using the existing kernel-inclusion instance.

For every relative test scheme `T` over `Spec k`, let `R` be its relative global-section algebra. `reducedNormHom_matrix_points` says that the actual reduced-norm character of a matrix-unit point, under the multiplicative-group point equivalence, is exactly `BinaryNorm.tensorNorm k D R` of its image under `MatrixPoints.tensorMatrixEquiv`. The proof unfolds the published character formula and cancels the actual coefficient algebra equivalence with its inverse. Thus the norm comparison is valid on every relative test, including nonaffine tests; it is not restricted to rational or geometric points.

## Kernel lifts

`liftPoint` takes an actual matrix-unit point together with a proof that its tensor norm is one, and constructs its point in the actual reduced-norm-one group using `kernel_isPullback.lift`. The square commutes because `Gm.pointsEquiv` is injective, preserves one, and satisfies the preceding norm-character comparison. `liftPoint_ι` is the pullback's first projection identity, so the lift has exactly the original point as image.

For an actual group-scheme homomorphism `f` into the canonical binary unit group, assume its tensor norm is one on every relative test point. `liftPoints` defines the corresponding group homomorphisms into the kernel on each test. The identity and product laws follow after cancellation of the monomorphic inclusion. `liftPoints_naturality` proves compatibility with every change of test by the same cancellation and associativity. `liftHom` applies the published group-valued Yoneda constructor to this natural family. `liftHom_ι` proves equality of the actual composite homomorphism with `f` on every test point, using the explicit naturality lemma and `liftPoint_ι`. This general lifting interface retains its explicit all-test norm-one premise; the elementary specialization below proves that premise.

## Elementary specialization and parameter coverage

Fix a basis `bD : Module.Basis (Fin d) k D`. The domain of `elementaryMap` is the actual vector group `FiniteAlgebraUnits.BinaryRoot.additiveScheme k`, of dimension `d`. The Boolean `false` selects the upper elementary family and `true` the lower family. `elementaryMap_tensorNorm` proves that the existing elementary family in the full unit group has tensor norm one on every test, using its actual tensor-matrix formula and `BinaryNorm.tensorNorm_upper` or `tensorNorm_lower`. No norm-one assumption is supplied by the caller of `elementaryMap`.

`elementaryMap` is the resulting actual homomorphism into the canonical reduced-norm-one group. `elementaryMap_ι` identifies its composite with the kernel inclusion with the published elementary homomorphism into the full unit group. `tensorMatrixEquiv_elementaryMap` consequently identifies every included point with the elementary matrix having parameter `tensorCoordinates k D bD T x`.

`exists_elementaryPoint` asserts that, for every relative test `T` and every element `a` of `R tensor_k D`, there is an actual vector-group point whose image under the included norm-one elementary map has precisely elementary matrix `a` in the selected orientation. Its proof uses the published surjectivity of `tensorCoordinates`, followed by the preceding evaluation formula. This is coverage of every elementary parameter, not surjectivity onto the whole norm-one group.

## Provenance and scope

The definitions and proofs are internal consequences of the actual constructions imported by this module. The norm-one identities descend from the published canonical reduced norm and splitting-field determinant comparison; the kernel and Yoneda steps construct actual scheme morphisms. This contribution does not construct cocharacters or contraction curves in the norm-one group, identify parabolic geometric radicals, prove local SK1 or a classification theorem, or prove the unrestricted local Kneser-Tits statement. Those remain separate obligations.
