# Tangent matrix operations and semisimplicity

This internal supporting unit concerns actual algebraic representations and their
actual dual-number differentials. It derives its results from the imported
matrix-point equivalence, dual and tensor representations, finite reindexing,
and the squarefree-minimal-polynomial criterion for semisimplicity. No external
structural assertion is assumed. It does not prove local semisimplicity of a
conjugation derivation or the Cartan-generation statement.

For a field `k` in any universe and an actual group scheme over `Spec k`,
`MatrixRepresentation.affineMatrix_eq_matrixUnit` reconstructs the matrix of an
actual tangent point as `I + εT`, where `T` is its tangent matrix. The proof
applies the published actual-point matrix equivalence to the identity
`pointKernelEquiv_tangentMatrix`. Consequently `affineMatrix_fst` identifies its
constant matrix with the identity.

`tangentMatrix_dual` identifies the differential of the actual dual
representation with minus the transpose of the original tangent matrix. It uses
the inverse of `I + εT`. `tangentMatrix_tensor_entry` computes the epsilon
coefficient of a product of dual numbers and gives the usual sum of the two
tensor differential terms. `tangentMatrix_reindex` proves compatibility with the
actual representation obtained by finite reindexing. These results allow any
finite indexing type in `Type`, as do the imported representation constructions.
No algebraic-closedness premise is used for these matrix identities.

Over an algebraically closed field,
`IsGeometricallySemisimpleMatrix.isSemisimple` descends matrix semisimplicity
from the algebraic closure. `algebraicClosureBaseEquiv` constructs the algebra equivalence given by the
algebra map to the algebraic closure. The proof transports the squarefree minimal polynomial
back along that equivalence, transports its annihilation identity, and applies
the squarefree-annihilating-polynomial criterion to the original matrix
endomorphism.

Finally `IsSemisimpleElement.isSemisimple_tangentMatrix` applies the original
representation-tested definition of a semisimple Lie element to any actual
representation with a finite indexing type in `Type`. It reindexes to a finite
ordinal, invokes that definition and the preceding descent lemma, and transports
semisimplicity back through the injective coordinate linear equivalence. This
last result retains algebraic closedness of the base field. All statements
preserve arbitrary characteristic and empty finite indexing types.
