# Length-ordered Weyl supports

This internal supporting construction enumerates the actual coordinate Weyl group
`Equiv.Perm (Fin n)` in decreasing inversion length. It supplies a finite increasing
support chain for the corrected support filtration, independently of the source
and target block shapes. It applies also to rank zero.

The construction merge-sorts an exhaustive finite list using the inversion count
from `LengthMinimality`. Sorting preserves membership and absence of duplicates,
so lookup gives a bijection from its finite set of positions to all permutations.
The sorted-list relation proves that inversion length is antitone in that position.

The support at a natural index consists of permutations whose position is smaller
than that index. The proofs establish monotonicity, the empty initial support,
the full support at the list length, and the exact singleton difference between
successive supports. Every prefix is closed under strictly increasing inversion
length. The newly added permutation has minimum length in the enlarged prefix;
equal lengths are allowed in any order.

These are finite combinatorial lemmas derived from the existing inversion-length
construction and Mathlib's list sorting and exhaustive-list equivalence results.
They assert no geometric quotient comparison or exactness of a representation
complex. The strict-length closure is the input used by the corrected two-sided
support construction to obtain its Weyl-invariant cores.
