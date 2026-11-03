# Actual standard-Levi split components contain root annihilators

Authors: Worker 1322, Worker 1320, and Worker 1327.

This derived supporting unit uses the actual standard-Levi representative and
actual split-component morphisms. It proves reverse containment in their real
cocharacter images, conditional on existing structural root-system premises.
It does not prove the opposite containment, Levi reductivity, or the unrestricted
`StandardLeviCentralDirectionsStatement`.

`StandardLeviSplitContainmentStatement` packages finite dimensionality of the
actual split component's real cocharacter space and existence of an actual
closed map to the ambient maximal split torus whose real map is injective and
contains the selected-root annihilator. It quantifies over arbitrary fields
and universes, with an affine ambient group. It retains finiteness of simple
roots and existence of a standard cocharacter for the selected set as premises.
`standardLeviSplitContainment` proves precisely this supporting statement.

For a closed representative `j : L → G` of the existing all-test standard Levi,
`standardLeviTorusFactor` lifts the ambient maximal split torus to `L` and remains
maximal split there. `IsSplitComponent.exists_commFactor_standardLevi` applies the existing
`IsSplitComponent.exists_commFactor_of_isMaximalSplitTorus` inside `L` to
construct a closed morphism `f : A → T`, injective on real cocharacters, for
each supplied split component `a : A → L`. Composing its factorization equation
with `j` gives the required ambient compatibility. This construction does not
require a root-system realization, genericity, or reductivity of `L`.

For any compatible actual morphism `f : A → T`, canceling the representing monomorphism shows that
`f` followed by this torus factor equals `a` in `L`.

`IsSplitComponent.rootAnnihilator_le_range_standardLevi` retains finiteness of
all simple roots and existence of a standard cocharacter for `J`. Those are the
precise premises of the existing standard-Levi annihilator centrality theorem.
They imply finiteness of `J` and centrality in `L` of every actual integral
cocharacter annihilating `J`. Applying the split-component central-cocharacter
bridge and its real integral-span criterion proves that `rootAnnihilator T J`
is contained in the range of the actual `cocharacterMapReal f`.

`IsSplitComponent.exists_commFactor_standardLevi_containing_annihilator`
combines the map construction and the reverse containment. Splitness of the
supplied component gives finite dimensionality via the existing finite-real-torus
result. The statement and its proof retain the finite-root and existence premises.

`IsSplitComponent.rootAnnihilator_le_range_standardLevi_of_rootSystem` derives
both structural premises from `HasRelativeRootSystem i`, ambient splitness,
genericity of `ν`, and `J` contained in the actual simple roots. It introduces
no additional rank, basis, or real-image assumption. The unrestricted root-system
realization remains a premise, and no reducedness or positive-rank restriction
is imposed.

The argument is internal to the Library's factorization, standard-Levi centrality,
root-system, and integral-annihilator span results; it uses no external source.
