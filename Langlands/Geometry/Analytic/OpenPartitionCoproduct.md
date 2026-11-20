# An analytic space partitioned into open domains is their disjoint union

Author: Worker 5254.

This module proves the statement `OpenPartitionCoproductStatement` (module
`OpenPartitionCoproductStatement`): an analytic space whose underlying space is
the disjoint union of open subsets `U j` is the coproduct, in
`LocalizedCategory`, of the open domains `U j` with their canonical morphisms
`domainι`. It is a helper for the proof of Berkovich's Example 1.2.1(i),
`InducedSpace.QuasiEtaleSiteEquivalenceStatement`, whose fullness and
essential surjectivity use this statement as the hypothesis `hP`. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation`.

Mathematically this is the case of pairwise disjoint open pieces of
Berkovich's gluing of morphisms over a quasinet (Berkovich, *Étale cohomology
for non-Archimedean analytic spaces*, Publ. Math. IHÉS 78 (1993), Proposition
1.3.2, printed p.24): an open cover is a quasinet, and the overlaps of distinct
pieces are empty, so every family of morphisms out of the pieces is
compatible and glues uniquely. The Lean proof below uses the Library's gluing
of morphisms over original-chart domain covers in the source-quotient model
`SourceCategory` of `LocalizedCategory`.

## Declarations

- `SourceCategory.eq_of_carrier_eq_empty E hE F G`: two morphisms of
  `SourceCategory` out of the original-chart domain `E` of a saturated
  presentation `A` are equal when `E` is empty (`hE : E.carrier = ∅`).
- `locallyRefines_openDomain Y U hU hc`: for open subsets `U j` (`hU`) of the
  space of `Y : LocalizedCategory.{u, v, w}` that cover it (`hc`), the
  carriers of the open domains `openDomain (U j)` locally refine the cover
  `{univ}` (the covering condition `AtlasTopology.LocallyRefines` used by the
  Library's gluing theorems).
- `openPartitionMatchingFamily Y U hU hd s`: for pairwise disjoint `U j`
  (`hd`) and a cofan `s` over the open domains, the matching family
  (`SourceCategory.QuotientDomainMatchingFamily`) on these domains whose local
  morphisms are the preimages, under the comparison equivalence
  `SourceCategory.comparisonFunctor : SourceCategory ⥤ LocalizedCategory`, of
  the legs `s.inj j`.
- `comparisonFunctor_map_openPartitionMatchingFamily_localMap`: the comparison
  functor sends the local morphism `j` of this family back to `s.inj j`.
- `isColimitOpenPartition Y U hU hd hc`: the cofan
  `Cofan.mk Y (fun j => domainι Y (openDomain (U j)))` is a colimit, i.e. `Y`
  is the coproduct of the open domains.
- `openPartitionCoproductStatement : OpenPartitionCoproductStatement.{u, v, z}`.

## Proof

`eq_of_carrier_eq_empty`: apply the Library's separation theorem
`SourceCategory.eq_of_domainCover` to the domain `E` itself with the empty
family of subdomains (index type `Empty`). Its covering condition is vacuous,
because the space of `E` has no points.

`locallyRefines_openDomain`: a point `x` lies in some `U j`; the one-element
family `{U j}` is finite, consists of a member of the cover, contains `x`, and
its union `U j` is a neighbourhood of `x` because `U j` is open.

`openPartitionMatchingFamily`: the overlap condition for indices `k`, `l` asks
that the two restrictions to the domain `U k ∩ U l` agree. For `k = l` the two
inclusions of `U k ∩ U k` into `U k` are equal, so the condition holds by
reflexivity. For `k ≠ l` the domain `U k ∩ U l` is empty by disjointness, and
`eq_of_carrier_eq_empty` applies.

`isColimitOpenPartition` (built with `Cofan.IsColimit.mk`):

- the morphism `Y ⟶ s.pt` is the image under the comparison functor of the
  Library's glued morphism `QuotientDomainMatchingFamily.glue` of the family;
- each leg is recovered: by `comparisonFunctor_map_domainInclusion` the
  canonical morphism `domainι` is the image of the source-category domain
  inclusion, and `glue_restrict` says the glued morphism restricts to the
  local morphism, which the comparison functor sends to `s.inj j`;
- uniqueness: a morphism `m : Y ⟶ s.pt` is the image of some source-category
  morphism `M` (the comparison functor is full). If `m` restricts to the legs,
  then, as the comparison functor is faithful, `M` restricts to the local
  morphisms, so `M` is the glued morphism by `glue_unique`.

`openPartitionCoproductStatement` applies `isColimitOpenPartition`.
