# Reduction of the global cuspidal target to a nonzero invariant form

This module proves
`cuspidalNonzeroTransposePairingReduction`, whose type is
`CuspidalNonzeroTransposePairingReductionStatement`. Its conclusion is
exactly the existing
`CuspidalTransposeInverseContragredientStatement`, with the field universe
free and all of its number-field, compact-quotient, rank and actual
cuspidal-realization quantifiers retained.

The explicit premise is `CuspidalNonzeroTransposePairingStatement`.
For every actual cuspidal realization `T`, it asks for a nonzero complex
bilinear form on `T.Space × T.Space` satisfying the existing
`T.realization.IsTransposeInvariantPairing` predicate. This retains finite
adelic, actual infinite compact, and actual real Lie invariance, with the
second variable twisted by inverse transpose and its real differential.
No injectivity, smoothness of partial functionals, or surjectivity onto the
contragredient functionals is included in the premise.

The implemented proof has three steps.

1. `IsTransposeIntertwining.isInvariantPairing_compl₂_symm` transports
   the three invariance identities along a supplied actual transpose
   equivalence. If that equivalence is `e`, the resulting pairing is
   `C(y, x') = B(y, e.symm x')`. Each identity follows by applying inverse
   covariance to the second variable.
2. For the actual equivalence `T.transposeEquiv`, the resulting `C` is
   nonzero: evaluating a proposed equality `C = 0` at `(y, e x)` forces
   `B(y, x) = 0` for all original vectors. The cuspidal nonzero-invariant
   pairing criterion then identifies `T.transpose` as a contragredient
   of `T`. That criterion uses existing cuspidal contragredient existence
   and a nonzero full-operator intertwiner between irreducible realizations,
   which is bijective by Schur's lemma.
3. Choose `T.transpose` and the vector `T.transposeEquiv x` for every
   original vector `x`. The existing `cuspFunction_transposeEquiv`
   equality supplies exactly the target's `dualFunction` formula.

The provenance is internal: the module combines the actual transpose
construction, the actual dual cusp-function comparison, and the
nonzero-invariant pairing criterion. It proves a conditional reduction
of the global target. Existence of the nonzero invariant transpose form
remains an unproved premise, including any local duality and tensor
assembly needed to construct it. This result does not prove the
unconditional global target.
