# Decomposition into all-test cocharacter row weights

Let `K` be any field, `D` a finite-dimensional division `K`-algebra, `σ` an
involution of the first kind, `n` a finite index type, and `q` a `σ`-quadratic
form. For every actual cocharacter `f : Gm → O(q)`, the published all-test
subspaces `cocharacterWeightSpace q f c`, indexed by integers `c`, form an
internal direct sum of the left `D`-module `n → D`.

The definition `cocharacterWeightDecomposition` is the resulting `D`-linear
equivalence from the row module to that direct sum. It is the inverse of the
canonical map adding the included components. Neither nondegeneracy of `q`,
centrality of `D`, infinitude of `K`, nor a characteristic restriction is needed.
The empty index type is included.

The implemented proof proceeds as follows:

1. `isometryRowActionOver_of_regular_eigenvector` works over every commutative
   coefficient algebra `R`. It translates the matrix of the inverse-right
   regular representation through the base-changed matrix-algebra basis. The
   resulting equation is multiplication in `R ⊗[K] Matrix n n D`. Applying
   `TensorMatrix.equiv` gives the same eigenvalue on every row.
2. `cocharacterCoefficientMatrix` converts a universal coefficient column of
   the regular representation of the one-dimensional split torus back into
   a matrix over `D`. The published
   `GeneralLinear.CocharacterDiagonal.coefficientColumn_weight`, specialized at
   the Laurent universal point, gives its integer eigenvalue. The universal
   detection equivalence for `cocharacterWeightSpace` then proves
   `cocharacterCoefficientMatrix_row_mem`.
3. The published `exists_coefficientBasis` supplies a basis of matrices of that
   form. Expanding a matrix whose rows equal a specified row shows that every
   row lies in the supremum of the weight spaces. For an empty row index the
   module is zero, handled separately.
4. Independence comes from `cocharacterWeightSpace_iSupIndep` in the companion
   coefficient-projector module. Together with spanning it gives
   `cocharacterWeightSpace_isInternal` and the displayed linear equivalence.

This is derived internal content: it combines the existing regular
representation, split-torus coefficient-basis theorem, tensor-matrix comparison,
and Laurent universal-point criterion. It introduces no additional claim from
the literature. It does not yet compare weight dimensions under field extension
or identify the weights of a spin cover with a numbered type-`D` root datum.
