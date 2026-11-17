# Proof of `ComplexPlaceMinusOneStatement`

Module: `Langlands.Global.RankinSelberg.ComplexPlaceMinusOneProof` (namespace
`Langlands.Global.RankinSelbergGlobal`).

Main theorem: `Langlands.Global.RankinSelbergGlobal.complexPlaceMinusOne :
Langlands.Global.RankinSelbergGlobal.ComplexPlaceMinusOneStatement.{u}`.

## What is proved

`ComplexPlaceMinusOneStatement` is the minus-one premise of the reduction
`ComplexPlaceFunctionalEquationReductionStatement` (module
`Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction`). It says: for every
number field `F` with compact adele quotient, every `r`, every actual cuspidal realization `T` of
`GL_(r+1)` over `F`, every complex place `w` and every list `d` of complex characters, if `T` has
the parameter `d` at `w` (`HasComplexPlaceParameter T.realization w d`), then

  `complexMinusOneScalar T w = complexCentralSign d`.

Here `complexMinusOneScalar T w` is the scalar by which `-1 ∈ U(r+1)` at `w` acts on `T`
(`1` by convention if it does not act by a scalar), and
`complexCentralSign d = (d.map fun d => d.character (-1)).prod = ∏_j χ_j(-1)`.

## Proof

The theorem applies `ComplexPlaceMinusOne.complexMinusOneScalar_eq_prod` from the helper module
`Langlands.Global.RankinSelberg.ComplexPlaceMinusOneScalar`. `complexCentralSign d` is by
definition the product it computes. That module's Markdown describes the argument:

1. `-1` at `w` is central in the infinite adelic group, because its archimedean coordinate
   matrix is a scalar matrix. So its compact operator commutes with the whole concrete operator
   algebra (finite adelic group, standard infinite compact and enveloping algebra), and each of its
   eigenspaces in `T` is a subrepresentation.
2. On the complex principal series of `d`, right translation by `-1 = diag(-1, …, -1)` is
   multiplication by `∏_j χ_j(-1)`.
3. The Library theorem `complexStandardNontrivial` gives a nonzero `U(r+1)`-finite function of
   that principal series. Its image under the injective equivariant map from the parameter is a
   nonzero eigenvector of `-1` at `w` with eigenvalue `∏_j χ_j(-1)`. By irreducibility of `T` the
   eigenspace is all of `T`, and `complexMinusOneScalar_spec` identifies the scalar.

The proof uses only the hypotheses of the statement and the axioms `propext`,
`Classical.choice` and `Quot.sound`.
