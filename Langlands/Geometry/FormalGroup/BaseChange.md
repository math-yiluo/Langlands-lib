# Change of coefficient ring and algebra-valued points

`CoordinateMap.map` applies an arbitrary commutative-ring homomorphism to
each coefficient. It respects composition, identity, zero, pairing and
projections, and respects identity and composite ring maps. `SeriesPoint.map`
does the same for substitutable tuples, preserving their substitution
condition. Coefficient change commutes with evaluation and pairing and
satisfies the identity and composition laws.

`CommLaw.map` constructs the scalar extension of a coordinate formal group
law by mapping its addition and inverse series. All formal-map identities
are transported by coefficient change. `CommLaw.mapPoints` constructs the
additive coefficient-change map on points. `CommLaw.Hom.map` constructs the
base change of a formal homomorphism.

`CommLaw.AlgebraPoint G A` is the additive group of points over a commutative
`R`-algebra `A`: take the base-changed law and evaluate on series with no
formal variables. Through `SeriesPoint.nilpotentEquiv` its underlying set
is the set of tuples of nilpotent elements of `A`. No completeness or
chosen convergence data on `A` is required. `algebraPointEquiv` supplies
the identification explicitly. `algebraMapPoints` constructs the additive
map for a homomorphism of coefficient algebras and proves its identity
and composition laws. `algebraPointFunctor` packages these constructions
as an actual functor from `CommAlgCat R` to `AddCommGrpCat`.

This is derived coefficient-change infrastructure for the formal groups
and formal modules in Drinfeld, *Coverings of p-adic symmetric regions*
(1976), §1, printed p.108; source ID
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The constructions are coordinate-level. No gluing theorem or
representability statement is asserted in this module.
