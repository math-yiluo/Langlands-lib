# Scalar subquotient detection from generalized dual spanning

Author: Worker 196.

The theorem
`Langlands.scalarSubquotientDualSpectrum.{uK,uA,uV,uW}` has the complete unapplied
type `Langlands.ScalarSubquotientDualSpectrumStatement.{uK,uA,uV,uW}` from
`Langlands.Representation.Exponents.ScalarSubquotientDualSpectrumStatement`.
It proves the generic scalar subquotient detection proposition by introducing
its binders and applying the helper
`Langlands.ScalarSubquotientDualSpectrum.scalarSubquotient_mem`.

The coefficient field, commutative acting group, ambient carrier and quotient
carrier have independent universes. No finite-dimensionality is used. Mathlib's
independence theorem for simultaneous maximal generalized weight spaces first
gives independence for distinct unit-valued characters. The helper
`independent_weights` restricts the indexing by functions to the injective
map from unit-valued characters to their scalar-valued functions. The helper
`generalized_le_weight` places each actual uniform generalized character
space in its simultaneous maximal generalized weight space; its finite bound
also supplies the bound for every individual group element.

The helper `dualRestrict_comp` proves that dual restriction to an actual
invariant subspace commutes with the transpose action. The helper
`restrict_generalized_le` uses this commutation to preserve maximal generalized
weights under restriction. Restriction is surjective over a field by
`Subspace.dualRestrict_surjective`. Mapping the assumed supremum through
restriction therefore proves that the predicate-indexed maximal generalized
weight spaces span the full dual of the invariant subspace.

Choose a nonzero quotient functional, whose existence follows from
nontriviality of the quotient carrier. Pulling it back through the actual
surjection gives a nonzero ordinary eigenfunctional on the invariant subspace
with the scalar quotient's character. It lies in the corresponding maximal
generalized weight space with exponent one. If this character were outside
the indexing predicate, independence would make that weight space disjoint
from the supremum of all indexed weight spaces. The latter supremum is top,
so that weight space would be zero, contradicting the nonzero pulled-back
functional. The transpose uses the same character, without inversion.

This is derived linear algebra using the existing full-dual and generalized
character-space constructions. It is not attributed as a verbatim theorem from
a representation-theory source and does not establish finite spectral
spanning, existence of irreducible scalar quotients, or any GL comparison.
