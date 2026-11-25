# Descent of compatible closed subgroup functors

This internal proof module generalizes the Library's all-test construction in
`SubgroupFunctor/ZariskiDescent` to an étale cover. The construction imposes each
local subgroup condition after every comparison of test schemes. Its local
base changes recover the given subgroups when their conditions match.

The absolute membership condition is a sieve on the ambient scheme.
For a monomorphically represented subgroup it is closed for the fppf topology:
factorizations through the monomorphism glue by subcanonicity. The universal
local condition defining the descended subgroup preserves this closure,
using pullback stability of covering sieves.

`isClosedRepresentable_etaleDescentSubgroup` assumes that every local subgroup
has a closed subgroup representative and that the all-test matching condition
holds. The induced étale cover of the ambient scheme is fppf. On each member,
absolute membership is represented by the supplied local closed immersion,
and after any further restriction by its pullback. The published
`fppfClosedLocusDescent` constructs a global closed immersion with this
membership condition. The Library's representability transfer equips its
source with a group structure and makes the inclusion a group homomorphism.
No affineness, finiteness, separatedness or nonemptiness of the base is assumed.

These are derived categorical support lemmas for descent in Conrad,
*Reductive group schemes* (2014), proof of Proposition 5.2.12, p.158.
They assert no existence of local opposite Borels or matching of such Borels.
