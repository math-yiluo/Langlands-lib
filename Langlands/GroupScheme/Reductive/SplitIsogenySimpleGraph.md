# Local-isogeny graphs indexed by source simple roots

This derived supporting construction specializes the actual local-isogeny graph
to the intrinsic simple roots of one generic source chamber. It follows the
source-side construction of `SplitLeviGluingSimpleGraph` and uses the actual
rank-at-most-one isogenies constructed in `SplitIsogenyLocalLevis`.

`SimpleIsogenyGraph` retains a split source torus, a generic chamber with a
rank-one kernel direction for each of its simple roots, the corresponding
target directions, actual local isogenies, and the generated graph. The target
directions are explicitly required to be pushforwards under the given torus
map. The index set consists of source simple roots.

`simpleIsogenyGraph` constructs all of this from the two connected reductive
groups, split maximal tori, their actual reduced root data, and a root-datum
isogeny at the field's characteristic exponent. It chooses the existing generic
source chamber and simple-root kernel directions. It applies `localIsogeny` in
each direction, using the coweight map for the target direction. The equation
`comp_torusMap` proves compatibility with the actual torus morphism. Thus no
local isogeny or graph is required among this constructor's inputs.

For each source simple root, the positive and negative representatives are
constructed in the same chosen source centralizer. Their lifts to the graph
are smooth connected affine closed subgroups. Their first projections
represent the full positive and negative intrinsic source root functors.
The graph torus normalizes these subgroups on every scheme test. The
source-root lift comparison from `SplitIsogenyRootGraphs`, followed by the
intrinsic root-to-dynamic inclusion, puts them in the positive and opposite
dynamic unipotent subgroups for the source chamber.

`source_coverage` is immediate from the annihilation property of the chosen
simple-root directions. For a source maximal torus in a connected reductive
group, its generic chamber centralizer is that torus. Applying the previously
proved graph projection theorem now proves that the first projection is flat,
surjective, locally of finite presentation and quasi-compact over the original
field.

The construction permits every universe and arbitrary fields. Its local maps
retain the given characteristic-power root factors and possibly nonsmooth
kernels through `localIsogeny`. It does not identify the target simple roots,
prove commutation of distinct positive and negative graph root subgroups,
establish a dense graph cell or maximality of the graph torus, or prove the
general realization or fixed-torus extension theorem.
