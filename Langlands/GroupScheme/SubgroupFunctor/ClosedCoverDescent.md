# Closed subgroup descent along covering families

This derived construction generalizes the Library's all-test Zariski subgroup
descent to arbitrary covering families, and proves closed representability
for matching families on fppf and étale covers. Its geometric input is the
published `Langlands.AlgebraicGeometry.fppfClosedLocusDescent`, together with
the published transfer of a scheme representative of subgroup membership to
a group scheme. It introduces no new assertion from external literature.

Let `G` be a group scheme over an arbitrary scheme `S`, let `𝒰` be a covering
family, and let `F i` be subgroup functors of the pullbacks of `G` to its
members. `CoverDescent.IsMatching 𝒰 F` requires compatibility under every
comparison of relative test schemes over `S`. A point in one local subgroup
must remain in the other local subgroup after restriction and the canonical
base-change point identification. This is the same all-test condition as
the published Zariski `SubgroupFunctor.IsMatching`, with the open cover
replaced by an arbitrary cover.

`CoverDescent.subgroup 𝒰 F` is the subgroup functor whose points satisfy each
local subgroup condition after every relative restriction to a member of
the cover. The group laws and restriction maps follow from those of `F i`.
`baseChange_subgroup` proves that a matching family is recovered exactly on
each cover member. These definitions and the recovery theorem use no
particular topology.

`membershipSieve F` expresses absolute membership as a sieve on the
underlying scheme of the ambient group. If each local `F i` has a closed
representative, `isClosed_membershipSieve_subgroup` proves that the global
membership sieve is closed for the fppf topology. To prove membership after
an fppf covering sieve, fix a restriction to a local base and pull the
covering sieve back to that test scheme. The local represented condition
gives local lifts through its closed immersion. The published
`FppfClosedLocusDescent.exists_lift_of_covering` glues those lifts, using
monomorphy and subcanonicity. The global all-test definition then gives the
desired membership.

`exists_closedRepresentative_pullback` verifies directly by the pullback
universal property that closed representatives of a sieve are stable under
arbitrary base change. `exists_closedRepresentative_of_cover` packages
the published closed-locus descent theorem for a covering family whose
generated sieve is fppf covering. A member of the generated sieve factors
through a cover member, so the preceding pullback result supplies the local
closed representative required by that theorem.

`isClosedRepresentable_subgroup_fppf` applies this result to the cover
induced on the ambient scheme by an fppf cover of `S`. The recovery theorem
identifies the membership condition there with the given `F i`; their
closed representatives supply local closed subschemes. Closed-locus
descent and representability transfer produce a global closed subgroup
scheme. `isClosedRepresentable_subgroup_etale` applies the fppf result
after viewing each étale morphism as flat and locally of finite
presentation.

`closedRepresentativeFppf` and `closedRepresentativeEtale` choose actual
global closed subgroup data. Each chosen homomorphism represents the global
all-test subgroup. Its base change represents `F i`, by
`IsRepresentedBy.baseChange` and `baseChange_subgroup`. The choice of
representative is noncanonical, while the global subgroup functor is given
explicitly.

There are no additional smoothness, affineness, finite-type, separatedness
or reducedness hypotheses on `S` or `G`. These results descend closed
subgroup membership. Preservation or descent of the relative Levi
predicate is a separate obligation.
