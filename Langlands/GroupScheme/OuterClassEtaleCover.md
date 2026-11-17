# Finite outer-class carriers from an étale trivializing covering family

This internal derived module adapts an actual étale covering family to the
single surjective trivialization used by `ofEtaleTrivialization`. The common
universe is arbitrary.

Let `R` be a commutative domain DVR with its specified fraction field `K` and
algebra structure. Fix group schemes `G`, `H`, and `A` over `Spec R`, a supplied
representing isomorphism scheme for `G` and `H`, and an action of `A` on `G`.
Assume the structure morphism of a supplied outer quotient `O` is separated.
Supply a jointly surjective étale covering family of `Spec R`, together with,
for each cover member `U`, the existence of a type `J` and an actual
isomorphism over `U` from the pullback of `O.parameter` to the coproduct of
`J` copies of `U`. The type `J` may be infinite and may vary with the member.

`FiniteGenericOuterClass.ofEtaleCover` chooses the member whose image contains
the closed point. Its morphism is étale and hence open. Every point of a local
spectrum specializes to the closed point, so an open image containing that
point is the whole base. The chosen member is therefore itself surjective.
The proof applies `surjective_of_isOpenMap_of_closedPoint_mem` to the covering
family's explicit precoverage-membership condition. It chooses the index type and trivialization only
on this one member and applies `ofEtaleTrivialization`.

The result is an actual finite carrier for the class of the exact specified
fraction-field point `p` of the isomorphism scheme. It has the base as its
finite relative scheme and retains the original fraction-field algebra map.
There is no need to combine different local index types into one global type,
and neither connectedness nor quasi-compactness of the cover members is
assumed.

`FiniteGenericOuterClass.ofComparisonEtaleCover` allows a second outer quotient
`O'` of the same represented functor and action to supply separatedness and
the trivializing covering family. It constructs the carrier for `O'` and uses
`ofComparison` to obtain one for the original `O`, preserving `p` and the
exact outer-class equation. No separatedness premise is added for `O`.

The provenance is the internal composition of the imported closed-point
surjectivity lemma, Mathlib's actual covering-family API, and the supplied-data
finite-carrier constructors. No external mathematical assertion is added.
Reductivity is unnecessary for this conditional result. Existence of a
separated outer quotient with such a trivializing family remains an explicit
input; the module does not prove the unchanged
`FiniteGenericOuterClassExistenceStatement` or add hypotheses to it.
