# Determinant reduction of the principal-norm formula

This module proves the algebraic norm identities needed to derive the principal
adele formula from the canonical completed tensor-product decomposition. It
proves the infinite-place principal formula without an extra hypothesis. Its
finite-place and full adelic formulas explicitly require bijectivity of the
actual finite tensor maps. It does not prove that remaining hypothesis or the
complete `NormCompatibility` proposition.

`norm_baseChange` chooses a finite basis over the base field. Left multiplication
by `1` tensor `x` is the scalar extension of left multiplication by `x`.
The matrix is therefore obtained by applying the scalar homomorphism entrywise,
and the determinant commutes with that operation.

`norm_prod` identifies left multiplication on a product algebra with the
product of the two left-multiplication maps and applies the block determinant
formula. `norm_pi` extends this to a dependent finite family of algebras, whose
dimensions need not agree. The proof uses finite-type induction: the empty
product is trivial, adjoining one index is the binary product formula, and
reindexing is an algebra equivalence preserving the norm. `norm_tensor_pi`
combines this with invariance of the determinant norm under algebra equivalence
and scalar extension.

At infinity, `infiniteNorm_principal` applies these identities to
`infiniteTensorEquiv`, whose bijectivity was proved in `Norm.lean` by weak
approximation and the local-degree sum. Its formula on `1` tensor `x` is the
diagonal image of `x` in each genuine completed extension. Thus the product
of local norms equals the image of the genuine global field norm, including
when `x` is zero.

`finiteNorm_principal_of_bijective` is the same determinant argument for the
canonical finite tensor map, with its bijectivity as an explicit premise.
The premise is not an arbitrary proposed map or norm. Combining the infinite
and finite coordinate formulas proves
`adeleNorm_principal_of_finiteTensorMap_bijective` and then
`principalNormCompatibility_of_completedTensorComparison`. This identifies
the proof dependency between the two proposition definitions in
`NormStatement.lean`; it does not discharge the completed tensor comparison.
All number-field results retain independent source and target universes.

The source of the determinant identities is Andre Weil, *Basic Number Theory*,
second edition (1973), Chapter III section 3, printed pp. 53-54
(PDF pp. 70-71). The completed tensor-product decomposition and the resulting
local/global norm formula are Chapter III section 4, Theorem 4 and Corollary 3,
printed pp. 56-58 (PDF pp. 73-75). The adelic product is Chapter IV section 1,
Corollary 3, printed p. 64 (PDF p. 81). Registered original:
`weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
The original passages were read; the Lean proof uses the finite-basis matrix
and finite-type induction arguments described above.
