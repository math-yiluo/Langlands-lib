# Irreducibility at equal real block exponents

`Langlands.Archimedean.realTemperedStandardIrreducible` proves
`Langlands.Archimedean.RealTemperedStandardIrreducibleStatement`. For every
natural number `n` and list `ds` of real blocks of total rank `n` with pairwise
equal real exponents, the actual `O(n)`-finite functions of
`realStandardModule n ds` form an irreducible module under
`realStandardRep n ds` and `realStandardLie n ds`. This includes the empty
list at rank zero.
[Library statement](RealTemperedIrreducibleStatement.md)

The Lean proof applies `realTemperedStandardIrreducible_of_form_of_scalarCommutant`
to `realTemperedForm` and `realTemperedScalarCommutant`. The form theorem gives
nontriviality and an anisotropic sesquilinear form invariant under `O(n)`, with
a scalar term in the real Lie adjoint identity. Using compact finiteness and
evaluation along compact orbits, the reduction obtains an orthogonal
complement to each invariant subspace. The form identities make this
complement invariant under the compact and complexified Lie actions.
Projection along the complement commutes with both actions, so the commutant
theorem makes it multiplication by a scalar. If the scalar is zero, the
projection has zero image. If the scalar is nonzero, multiplication by its
inverse shows that every vector lies in the projected subspace. With
nontriviality, this gives irreducibility.
[Invariant form](RealTemperedFormProof.md),
[scalar commutant](RealTemperedScalarCommutantProof.md),
[irreducibility criterion](RealTemperedCommutantReduction.md)

This is an internal composition of the published form and scalar-commutant
theorems. It establishes irreducibility independently of the Langlands quotient
theorem and tied Langlands classification.
