# Restricted split retraction and coefficient intersection

This is an internal algebraic and topological prerequisite for compact
induction in stages. It removes an intermediate subgroup from the actual
kernel and coefficient intersections. It asserts no integral comparison or
normalized p-adic orbit isomorphism.

Let `r : G →* L` and `s : L →* G` satisfy `r(s(l)) = l`. Let `P` contain
`ker r`, and let `H ≤ P`. No subgroup is assumed open, closed or normal.
The group, scalar and coefficient universes are independent.

`splitStagesRetraction : P →* P.comap s` sends `p` to `r(p)`.
Its membership proof is the published `splitQuotient_section_mem`, through
`splitQuotientRetract`. Its section is `s.subgroupComap P`, and its kernel
is `r.ker.subgroupOf P`. The retraction and section are continuous when
the original maps are continuous, for the actual induced topologies.

Write `rP` for this restricted retraction, `HP = H.subgroupOf P`,
`I = HP.comap rP.ker.subtype`, `J = H.comap r.ker.subtype` and
`N = r.ker.comap H.subtype`. The maps `splitStagesKernelEquiv`,
`splitStagesIntersectionEquiv` and
`splitStagesCoefficientIntersectionEquiv` remove the intermediate subtype
and, for the last map, switch the order of the two remaining inclusions.
Their inverse maps insert the subgroup membership proofs supplied by
`ker r ≤ P` and `H ≤ P`. They preserve the actual ambient group element;
the inverse and multiplication laws follow by reflexivity.

For any commutative ring `R` and any `R`-linear representation `σ` of `H`
on an arbitrary module, `splitStagesCoefficientEquiv` identifies
`Representation.Coinvariants ((σ.comp φ).comp j)` with the actual
`Jacquet.Coinvariants σ N`. Here `φ : HP →* H` is the canonical
`subgroupOfEquivOfLe` homomorphism and `j : I →* HP` is the restricted
kernel inclusion. Each map descends the identity on vectors using the
actual quotient lift. The intersection equivalence identifies its generating
relations, and induction on quotient representatives proves the two inverse
laws. Both representative formulas retain the original vector.

`splitStagesIntersectionMap` restricts every coefficient intertwiner to
the nested intersection. The quotient equivalence commutes with this map
and the actual `Coinvariants.map` restricted to `N`, for coefficient
modules in independent universes. No smoothness or dimension condition is
needed.

If `s(l) ∈ H` for every `l ∈ P.comap s`, then
`splitStagesInducingSection` is the original section with values in `H`.
The section formula for the coefficient equivalence uses the actual action
`(σ.toCoinvariants N).comp splitStagesInducingSection`, and preserves the
class of `σ(s(l))v` on every representative.

For arbitrary topologies on `G` and `L`, the three group equivalences
are bundled as continuous group equivalences by composing subtype
inclusions. These facts do not require continuity of `r` or `s` or
topological group operations: all these identifications retain the same
ambient element. The earlier retraction and section continuity results
do require continuity of their respective original maps.

All declarations here are derived from the published split quotient
construction, Mathlib subgroup inclusions and actual coinvariant quotients.
They are internal transport lemmas rather than a theorem quoted from
literature. They isolate the subtype bookkeeping needed by the relative
integral application; measure compatibility, Haar scaling, integration,
compact support and normalization remain separate obligations.
