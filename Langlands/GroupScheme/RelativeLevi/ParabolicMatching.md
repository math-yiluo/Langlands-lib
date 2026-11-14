# Ordinary matching of actual parabolic families

Worker 610. This derived internal module connects ordinary presheaf matching
of relative parabolic families with the all-test subgroup matching used by
`ParabolicZariskiDescent`. For a reductive group over any scheme, local actual
parabolic families on any open cover of a parameter scheme have a unique
actual global parabolic family whenever their restrictions agree on every
common comparison over that parameter scheme. All constructions work in
every universe and use equality of subgroup functors on all tests.

The module reuses the generic `TorusSubgroupModuli.familyPointsEquiv` and its
projection and naturality laws from `HomScheme.AdmissibleRestrictionPoints`.
`restrict_val_eq` identifies parabolic restriction with actual subgroup base
change followed by inverse transport along the canonical ambient pullback
comparison. `mem_restrict_iff` and `mem_restrict_of_original` express membership
through that generic point adjunction. `mem_of_restrict_eq` transfers membership
between two families with equal restrictions and points having equal projection
to the original ambient group. Its proof uses the identity relative test over
the common parameter scheme and uniqueness of the point in an actual pullback.

`isParabolic_comapIso` transports a relative parabolic representative along an
ambient group isomorphism. `coverSubgroup` uses it to express each local family
inside the iterated ambient pullback, as required by generic subgroup descent.
`IsMatchingParabolic` is the ordinary matching condition: restrictions along
any two morphisms into cover members are equal when their composites to the
parameter scheme are equal. `isMatching_coverSubgroup` converts it into
`SubgroupFunctor.IsMatching`. For every comparison of relative test schemes,
it applies ordinary matching over the underlying test scheme and uses the
point-adjunction projection identities to transfer actual membership.

`baseChange_eq_comap_restrict` identifies ordinary base change with family
restriction and the direct-to-iterated ambient comparison. Consequently,
`eq_of_restrict_cover` detects equality of actual families on the parameter
cover. `matchingSubgroup` is the generic descended subgroup of the
`coverSubgroup` conditions. Its local base changes recover those conditions,
and its membership is Zariski local. `restrict_matchingSubgroup` recovers the
original direct local families after cancelling the two ambient comparisons.

`isParabolic_matchingSubgroup` applies effective all-test parabolic descent
in the reductive ambient group over the parameter scheme. `matchingParabolic`
packages that same subgroup with its resulting parabolicity proof.
`restrict_matchingParabolic` records ordinary local recovery, and
`existsUnique_restrict` combines it with equality detection to give unique
gluing. No further effectivity hypothesis is required.

The point and matching arguments adapt the published implementations in
`HomScheme.AdmissibleRestrictionPoints`, `AdmissibleMatching`, and
`AdmissibleDescent` to the unchanged relative-parabolic predicate and its
explicit reductivity hypothesis. Effective parabolicity comes from
`RelativeLevi.ParabolicZariskiDescent`. These are derived constructions from
the imported Library results, rather than additional source assertions.
Smooth proper representability and descent across an etale cover remain
separate obligations.
