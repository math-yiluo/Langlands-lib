# Centralizer congruences for an actual ambient torus

This derived module treats an affine commutative group scheme `T` over a
nonarchimedean local field `F`, supplied parahoric-building data `P` for `T`,
a field extension `L/F` that splits `T`, and an additive real valuation on `L`.
It keeps exactly `P.centralizerZero` at depth zero. At positive depth it
intersects that subgroup with the inverse image, under the actual centralizer
inclusion, of the ambient extended-character congruence subgroup.

The family decreases with depth. A point in every subgroup satisfies all
ambient extended-character conditions, since the condition at `r+1` implies
that at `r`. Split-torus character separation and injectivity of the closed
centralizer inclusion give the identity. These facts construct an actual
`P.CentralizerFiltration`, without changing the supplied zero datum.

The ambient group is commutative and the chosen split torus has no relative
roots, by `ValuationBuildingData.relativeRoots_eq_empty_of_commutative`.
The root compatibility and the ordinary and double-root friendliness clauses
are therefore vacuous. Ambient conjugation is trivial, so the filtration
images are normalizer stable. Injectivity of the centralizer inclusion reflects
commutativity, so commutators of all its filtration subgroups are trivial.
Thus all four algebraic filtration axioms hold.

When `L` is an ultrametric normed field, its inclusion from `F` is continuous,
and the additive valuation is the logarithmic norm valuation with positive
scale, this filtration is open. The published theorem
`ParahoricBuildingData.centralizerZeroCompactOpen` supplies openness of its
actual zero subgroup. The published `rationalCharacterLattice` theorem
supplies finite generation of the extended character module, since the
extended torus is split and connected reductive. Continuity of the actual
centralizer inclusion and of scalar extension then pulls back the open
character conditions at positive depth. All rational-point topologies in this
argument are exactly their canonical `rationalPointTopology` instances.

Finally, `exists_doubleRootFriendly_filtration_of_torus` gives the full
existence conclusion for every actual `F`-torus `T` and every
`P : ParahoricBuildingData T.toGrp`, at arbitrary universe and in either
characteristic. No splitting field or filtration is a premise: the published
`torusFiniteGaloisSplitting` theorem supplies a finite Galois splitting field.
`LocalField.FiniteExtension.normedField`, `normedAlgebra`, and `ultrametric`
equip it with its actual spectral norm, for which scalar inclusion is
continuous. The construction uses logarithmic scale one and the preceding
algebraic and openness results. It needs no additional apartment-axiom
hypothesis in this torus case.

This module is internal infrastructure and a torus case of the host problem.
It does not construct the filtration for an ambient group with roots.
