# Degree bounds from the reduced characteristic polynomial

This internal deduction concerns a field `K` and a finite-dimensional
central division `K`-algebra `D`, in any common universe and any
characteristic.

`aeval_reducedCharpoly`, imported from
[ReducedCharpolyDivision](ReducedCharpolyDivision.md), proves that the canonical reduced characteristic
polynomial annihilates an original element `a : D`. The regular
characteristic polynomial is its reduced-degree power. Cayley–Hamilton
for left multiplication, followed by evaluation at `a`, makes that
power zero. A division ring has no nonzero nilpotents, so the value of
the reduced characteristic polynomial is zero.

`minpoly_dvd_reducedCharpoly` applies the defining divisibility property
of the minimal polynomial. The definition
`reducedCharpolyMinpolyQuotient` is the canonical Euclidean quotient of
the reduced characteristic polynomial by that minimal polynomial.
`minpoly_mul_reducedCharpolyMinpolyQuotient` proves that multiplying
the minimal polynomial by this quotient recovers the reduced
characteristic polynomial exactly.

`minpoly_natDegree_le_reducedDegree` bounds
its degree using divisibility, monicity and the known degree of the
reduced characteristic polynomial. The theorem
`residueGeneratorSubalgebra_finrank_le_reducedDegree` expresses the same
bound as a dimension bound for the original commutative singleton
adjoin, with its existing field structure.

For an actual nonarchimedean local field with the supplied valuative
relation and topology, `localDivisionResidue_finrank_le_reducedDegree`
proves that the actual residue extension has degree at most the reduced
degree. It uses `localDivisionResidueField` and exactly
`localDivisionResidueAlgebra`, and selects the already constructed
full-residue subfield whose degree is the actual residue degree. The
singleton-adjoin bound applies to that original subfield.

The proof uses the published reduced characteristic polynomial,
Mathlib's Cayley–Hamilton theorem and minimal-polynomial properties, and
the published local full-residue subfield construction. It asserts no
new external source result. It does not prove the reverse residue
degree bound, maximality or cyclicity, arbitrary-element movement or
local SK1.
