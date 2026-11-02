# Literal-intersection compact-open basis predicates

This module supplies internal vocabulary for the actual-group statement of
Renard V.5.2(i)–(ii), printed 123/PDF 129 in the registered 9 July 2026 edition,
`renard-2026-representations-groupes-reductifs-padiques`. These are S20 and the
ordered-product part of S21 in the
[Chapter V source map](../../../notes/renard/chapter-v-structural-inputs.md).
The inherited-family condition expresses standard-Levi compatibility using the
same literal intersections, in the setting of V.5.1(5).

`orderedIntersectionProduct K M N Nbar` is the function from
`(K ∩ Nbar) × (K ∩ M) × (K ∩ N)` to `K` whose value is the actual ambient
product `(nbar * m) * n`. The proof that its value lies in `K` uses only closure
under multiplication. `HasIwahoriIntersectionDecomposition` says this function
is bijective. Its surjectivity is the ordered setwise-product equality with
`K`, and its injectivity is the intrinsic uniqueness law. Neither a chosen
factorization map nor a group equivalence with the direct product is assumed.
The multiplication is not claimed to preserve the direct-product group law.

`CompactOpenNormalBasis K0 B` says that each member of one family `B` is
contained and normal in the same fixed subgroup `K0`, and has compact open
carrier in the ambient topology. Its `HasBasis` clause describes the entire
identity-neighborhood filter: the carriers are neighborhoods and every
identity neighborhood contains some member. In the actual application,
`K0` must be the geometrically defined special maximal compact from the shared
KP setup, and the topology must be the canonical rational-point topology.
The predicate itself neither chooses that subgroup nor asserts any generic
existence theorem.

`intersectionFamily M B` contains precisely the subgroups
`Subgroup.comap M.subtype K` for `K ∈ B`. Thus its elements are the literal
intersections `K ∩ M`, with the induced subgroup topology. The predicate
`InheritedCompactOpenNormalBasis` asserts that this same family is a compact
open normal neighborhood basis relative to the literal `K0 ∩ M`. It does not
allow a separate unrelated basis choice for each Levi.

These definitions are internal encodings of the cited source clauses and the
task's explicit uniqueness and compatibility requirements. They establish no
S20 existence, no S21 decomposition, and no S22–S23 contraction result. The
actual-group wrapper must quantify the single basis before every standard
parabolic, apply the predicates to the actual standard subgroups, and combine
them with the character-defined contraction conditions. Constructing the basis
from actual valued-root filtrations, proving simultaneous decompositions and
normality, and identifying all standard-Levi structures remain mathematical
obligations. The smaller normal subgroups here are not a chamber Iwahori.
