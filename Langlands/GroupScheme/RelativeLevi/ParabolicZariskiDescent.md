# Effective Zariski descent of actual parabolics

This derived internal construction descends matching actual
relative parabolic subgroup functors of a reductive group over a base open
cover. It works over any base scheme and in every universe. The matching
hypothesis is the published all-test condition `SubgroupFunctor.IsMatching`;
no closedness, affine-base, finite-cover or supplied global-representative
hypothesis is required.

`isZariskiLocal_of_isParabolic` obtains locality of membership on every test
scheme from a monic parabolic representative. `isParabolic_of_openCover`
first uses `SubgroupFunctor.exists_isRepresentedBy_of_openCover` to construct
a global monic group-scheme representative from local ones. It then applies
`isParabolic_of_isRepresentedBy_of_openCover`, which detects relative
parabolicity of that inclusion on the base cover. Thus it also proves
parabolicity of any Zariski-local subgroup functor whose restrictions are
parabolic.

`isParabolic_descentSubgroup` applies this argument to the published
`descentSubgroup`: its membership is Zariski local because each local
parabolic is monically represented, and its base changes equal the given
local subgroups by `baseChange_descentSubgroup`. `descentParabolic` packages
this same all-test subgroup with the resulting parabolicity proof.
`baseChange_descentParabolic` records local recovery.
`eq_descentParabolic` proves uniqueness among actual parabolic subgroup
functors using equality detection on an open cover.

The construction is derived from the generic subgroup descent in
`Langlands.GroupScheme.SubgroupFunctor.ZariskiDescent`, monic gluing in
`Langlands.GroupScheme.SubgroupFunctor.MonicGluing`, and locality in
`Langlands.GroupScheme.RelativeLevi.ParabolicLocality`. Its relative-parabolic
predicate is the unchanged one from `RelativeLevi.Basic`; the ambient group
is explicitly assumed reductive where parabolicity descends. This module
does not construct a parameter scheme or prove smooth proper
representability. The connection of ordinary presheaf matching to the
all-test matching hypothesis used here is made in `ParabolicMatching`.
