# Open subspaces and compactness of finite scheme sources

Author: Worker 133.

This internal construction packages existing representable-open subfunctor
results as actual algebraic spaces and proves two geometric transport facts
needed by finite-surjective AF descent. It introduces no axioms or descent
premises and does not prove AF descent.

## Actual open subspaces

In namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubspaceGeometry`,
`openSubspace Y A hA` is the algebraic space associated to a subfunctor
`A : Subfunctor Y.presheaf` whose inclusion is a representable open immersion.
Its presheaf is exactly `A.toFunctor`.

The construction uses the published `OpenSubfunctorImages.isSheaf_of_open`
and `OpenSubfunctorLifting.open_subsheaf_isAlgebraicSpace`. Thus the
subfunctor is an actual fppf sheaf with representable diagonal and an
etale geometrically surjective scheme atlas. `inclusion` is the actual
algebraic-space morphism induced by `A.ι`, and
`inclusion_isOpenImmersion` records its original open-immersion witness.
The base scheme is arbitrary.

`isQuasiSeparated_openSubspace` proves that the existing relative
quasi-separatedness of `Y` passes to this open subspace. The implemented
proof uses the cartesian diagonal square of the monomorphism `A.ι`,
from `OpenSubfunctorImages.diag_isPullback_of_mono`, and stability under
base change of the represented quasi-compactness predicate.

## Compactness of finite scheme sources

`compactSpace_of_finite_source` starts with an actual scheme `U : Over S`,
an algebraic space `Y` with `IsQuasiCompact Y`, and an actual presheaf map
`a : (schemeYoneda S).obj U ⟶ Y.presheaf` satisfying the existing `IsFinite`
predicate. It proves `CompactSpace U.left`. It needs neither surjectivity
of `a` nor quasi-separatedness of `Y`.

The proof chooses the compact etale surjective atlas `V` of `Y`, and
represents its pullback by the finite map as a scheme `W`. The projection
`W → V` is finite, so `W` is compact. The other projection `W → U` is
surjective because the atlas is geometrically surjective. Fullness of the
relative scheme Yoneda functor realizes this projection as an actual
scheme morphism. Its continuous surjective point map then makes `U`
compact.

These results are internal consequences of the named Library APIs and
Mathlib's scheme quasi-compactness and topological compactness results.
They supply no approximation, normalization, conductor square, AF pushout,
quasi-affine-source descent proof or final scheme representability theorem.
