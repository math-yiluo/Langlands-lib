# Compatible maximal tori for subgroups of split-torus centralizers

Author: Worker 1352.

This internal construction proves compatible actual split maximal-torus
existence for a closed subgroup `d : D ⟶ M` of any all-test representative
`j : M ⟶ G` of the centralizer of a split subtorus `a : A ⟶ G`. The base
field is algebraically closed, and `G` is affine and locally of finite type.
No normality, derived-subgroup, semisimplicity or reductivity hypothesis is
needed for this construction.

`SplitTorusCentralizerSubgroupTorusModel` contains a
`SplitTorusCentralizerRootModel a j`, an actual split maximal torus
`t : S ⟶ D`, and a closed morphism `S ⟶ T` into that model's torus. Its
composite into `M` is exactly `t ≫ d`. The companion
`inclusion_ambient_comp` gives the resulting equality after composition
with `j`.

To construct the model, first choose a maximal torus of `D` and extend it
inside `M` by `exists_maximalTorus_extension_of_finiteType`. All these tori
split by finite Galois splitting over the algebraically closed field. The
canonical factor of `A` into `M` is central, so
`IsMaximalSplitTorus.exists_factor_of_commute` factors it through this
chosen maximal torus of `M`. Extend that torus into an ambient maximal
torus of `G`. The factorization of `A` through this extension lets the whole
extension factor through `j` on every test scheme. Ambient maximality then
gives maximality in `M` by `IsMaximalTorus.of_comp`. Closedness of the maps
from `A` and `S` is obtained by cancelling closed embeddings from their
known closed ambient composites. Classical choice selects a model from
the proved nonempty model type.

The provenance is an explicit composition of these existing Library
constructions, plus centrality of `torusCentralizerFactor`. It applies in
particular to the actual derived subgroup required by
`SplitTorusCentralizerDerivedCorootComparisonStatement`, because an
`IsDerivedSubgroup` inclusion is closed. The unit establishes the actual
tori and morphism square only. Root-datum existence and equality of the
integral images of coroot spans remain separate obligations.
