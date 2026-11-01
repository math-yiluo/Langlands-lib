# Selecting a least realized permutation

`Langlands.Combinatorics.permutationLexMinimum` proves the proposition
`Langlands.Combinatorics.PermutationLexMinimum` without any added hypothesis.

The proof enumerates the permutations of the given integer word `w₀`,
converts the enumeration to a finite set, and filters it by the supplied
predicate `P`. This finite set is nonempty because `w₀` is its own
permutation and satisfies `P`. Classical decidability is used for the
filter, so `P` need not be decidable or computable.

The proof selects the minimum `w` of this finite set in the lexicographic
linear order on integer lists. Membership of the minimum supplies `P w`
and `w.Perm w₀`. For any other permitted `v`, membership in the same
finite set gives `w ≤ v`; this excludes `List.Lex (· < ·) v w`.

The implementation uses only the published proposition and Mathlib finite
set minima. The finite set may eliminate duplicate enumerations arising
from repeated entries; `List.Perm` still retains all entry multiplicities.
The empty input causes no exception, since its permutation enumeration
contains the empty word.

This is an elementary finite-order proof. It proves minimality only within
the fixed permutation class. Actual realization of the initial word and
all representation-theoretic local transfers remain outside its scope.
