# Quasi-splitness and torsor points at almost all finite places

`Langlands.GroupScheme.almostAllPlacesQuasiSplit` proves
`AlmostAllPlacesQuasiSplitStatement.{u}` for every universe `u`. For a connected
reductive group over a number field `F`, its base change to `F_v` is quasi-split
for all but finitely many finite places `v`. Every fpqc torsor under the group
has an `F_v`-point for all but finitely many finite places, with the exceptional
set allowed to depend on the torsor.
[Statement and source comparison](AlmostAllPlacesQuasiSplitStatement.md)

## Proof

The Lean term applies `almostAllPlacesQuasiSplit_of_henselian.{u}` to
`henselianFiniteResidueQuasiSplit.{u}`. For the quasi-splitness clause the
reduction spreads the group out over a ring of `S`-integers. Outside `S`, the
henselian theorem gives a Borel subgroup of the reductive model over the
completed integer ring. Restricting that subgroup to the generic fibre gives
a Borel subgroup of `G_{F_v}`.
[Henselian reduction](AlmostAllPlacesQuasiSplitHenselianReduction.md) ·
[Henselian quasi-splitness](../RelativeLevi/HenselianQuasiSplitProof.md)

For the torsor clause the reduction invokes
`AlmostAllPlacesTorsorPoints.eventually_nonempty_ringPoint_of_torsor`. The
torsor is smooth, separated, quasi-compact and geometrically connected.
The theorem on local points of such schemes uses spreading out and uniform
Lang–Weil bounds to give points over almost all finite completions.
[Torsor points](AlmostAllPlacesTorsorPoints.md)

## Source

Brian Conrad, *Reductive group schemes* (2014), Exercise 5.5.3(iii), printed
pp. 182–183, for number fields. Definition 5.2.10, p. 157, gives the
quasi-splitness convention. The registered source is
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
