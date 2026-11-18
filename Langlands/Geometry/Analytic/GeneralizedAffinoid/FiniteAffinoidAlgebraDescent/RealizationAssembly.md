# Assembling effective finite affinoid algebra realizations

This internal construction assembles the full published `EffectiveRealization`
from its remaining analytic outputs: a matching presentation, a finite Banach
bound for the original structural map into the matching algebra, and bounded
equivalences for every original base change whose entire forward maps are
the prescribed canonical comparisons. These are conditional inputs to the
assembly function. Their existence is still required to prove
`FiniteAffinoidAlgebraDescentStatement`.

`BoundedAlgHom.IsFiniteBanach.postcomp_equiv` proves that finite Banach bounds
transport along a bounded equivalence of target algebras. If the original
finite tuple is `b`, the transported tuple is `e(b)`. For an element `y` of
the new target, take the original controlled coefficient lift of `e.symm(y)`.
The coefficient equation follows by applying the algebra equivalence to the
finite sum. If the old lift bound is `M` and the inverse bound of `e` is `D`,
the new lift bound is `M * D`. This proof works over every normed coefficient
field and uses the supplied bounds explicitly.

`MatchingPresentation.finite_baseMap` applies this transport to the bounded
inverse of the matching presentation. Its converse `finite_matching` uses the
forward equivalence and cancels the inverse in the structural map. Thus
`finite_baseMap_iff` shows that the two required global finite Banach
conditions follow from either one with its actual norm-controlled lifts.
No argument upgrades algebraic module finiteness to Banach finiteness.

`effectiveRealizationOfComparisons` keeps the supplied matching presentation,
finite matching bound, and original comparison equivalences. It constructs
the presented finite Banach bound by `finite_baseMap`. The spectral assembly
module supplies whole-map overlap compatibility and the exact canonical
homeomorphisms on the entire quotient-glued spectrum and on every original
inverse-image locus. The projection theorem records that the matching
presentation is retained definitionally.

This module is derived from the explicit published descent interfaces and
bounded equivalence, coefficient-map, and spectrum constructions. It adds no
existence theorem for a matching presentation or effective original
comparisons, and imposes no strict-radius, nontrivial-valuation,
nonempty-spectrum, rational-cover, or ambient Hausdorff hypothesis.
