# Zero-subgroup data for a connected reductive unramified group

`UnramifiedZeroDatum.ofConnectedReductive` constructs an actual zero datum for
any supplied connected reductive group `H` over `UnramifiedClosure F`, where
`F` is a nonarchimedean local field in an arbitrary universe `u`.

The construction applies the published theorem
`simplyConnectedDerivedCoverExistence` to `H`. Classical choice selects its
actual derived subgroup, its simply connected covering group, and their maps.
`UnramifiedZeroDatum.ofDerivedCover` then supplies the maximal torus, its
embedded finite Galois splitting field, and the remaining datum fields.
The input connected reductivity is the only group-theoretic hypothesis.

This is an internal composition of existing Library results. It introduces no
additional literature assertion and makes no claim that the resulting choices
are canonical or that the zero subgroup is independent of them. It constructs
neither building data nor an integral model. In the Iwahori-model application,
simple connectedness after field extension supplies the required connected
reductivity.
