# Reductivity of smooth connected normal subgroups

`Langlands.GroupScheme.normalSubgroupReductive.{u}` proves
[`NormalSubgroupReductiveStatement.{u}`](NormalSubgroupReductiveStatement.md)
over every field in universe `u`. It installs the supplied smoothness and
connectedness of `N` as local instances and applies
`IsConnectedReductive.of_normalSubgroup` to the ambient reductivity, the
closed immersion `n : N ⟶ G` and the normality of its range.
[Normal subgroup reductivity](NormalSubgroup.md)

The invoked theorem obtains affineness from the closed immersion and
checks the unipotent radical after base change to the algebraic closure.
There the unipotent radical of `N` has normal range in the ambient group
on every test scheme. The ambient geometric radical is trivial, so the
composite range is trivial and cancellation of the subgroup inclusion
shows that the radical of `N` is trivial. Its greatest property then
gives the required triviality for every smooth connected unipotent normal
closed subgroup of the base-changed `N`.

The statement is Milne, *Algebraic Groups* (2017), Corollary 21.53
(printed p. 441, PDF p. 457), with the reductivity convention of 6.46
(printed p. 135, PDF p. 151). The retained source ID is
`milne-2017-algebraic-groups` and its SHA-256 is
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
