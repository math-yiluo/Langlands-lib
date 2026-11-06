# Actual torus buildings with all five metric-construction axiom families

This internally derived unit constructs actual `ParahoricBuildingData`, a
polysimplicial realization and an apartment splitting satisfying the seven
existing predicates in `RootValuationBuildingConstructionStatement`, for every
actual torus over every nonarchimedean local field and at every universe `u`.
It requires `IsTorus T.toGrp` and has no anisotropy, splitness, characteristic,
supplied-building or derived-cover premise. The unrestricted connected-reductive
parent statement remains open.

The supplied-data lemmas use any `ValuationBuildingData` or
`ParahoricBuildingData` for a commutative ambient group. The final constructor
`torusBuildingConstructionData` supplies that datum with
`ParahoricBuildingData.ofTorus`; all root valuations, zero subgroups, maximal
split tori, centralizers, covers and embedded splitting-field choices are those
actual constructors provide.

Commutativity makes every actual inner automorphism the identity and hence the
actual rational normalizer the full point group. The actual relative roots are
empty by the proved central-root restriction result. The existing root-free
fixer formula therefore makes the original reduced quotient a singleton. This
uses the actual quotient and action, without replacing either carrier or map.

Every norm-one point stabilizer is then exactly the original common rational
character norm kernel. Openness follows from the published norm-kernel openness
theorem in precisely `rationalPointTopology F T.toGrp.X`. Its compactness follows
from compactness of the norm kernel intersected with the full abstract centre:
for a commutative group that centre is the whole group. The published
compact-to-algebraically-bounded theorem supplies KP boundedness. The entire
torus point group need not be compact.

For KP 4.1.1 the existing empty-factor realization realizes the original unique
facet with its face order and action. The published largest-split-subtorus
universal property proves that all actual maximal split tori of a commutative
group are isomorphic over it; the resulting identity conjugacy gives every
required chart. The unique apartment and the unchanged normalizer-stabilizer
formula give the remaining clauses.

For KP 4.1.4 the derived group is the actual trivial group from
`commutativeDerivedCoverData`, and its maximal split torus is the actual trivial
commutative group with identity inclusion. Its inclusion into the original
maximal split torus is the zero homomorphism, a closed unit section. The central
factor is the whole original maximal split torus with identity inclusion; it
is the actual split component by centrality and maximality. The two real
cocharacter-map ranges are respectively bottom and top, giving the required
direct complement. The original normalizer preserves the derived factor, its
action on the point apartment is trivial, and the existing general affine
conjugation theorem gives the final field. These prove all nine existing fields.

AS1 has no root-indexed cases. The published root-free apartment theorem gives
V6, V7 and all of AS2–AS5, including the normalizer automorphism inclusions and
equalities. The root-free actual-quotient facet theorem gives AS6. Finally the
existing trivial-Weyl construction proves all six Tits fields for every original
chamber, using the original zero subgroup and full normalizer. It uses the
Library's documented empty-reflection extension of the restricted Tits building.

The final data-valued dependent pair packages the actual datum, realization and
splitting with precisely the seven unchanged predicates. This proves the full
torus specialization, with no assertion of the general parent theorem, a
metric-space construction, or unramified descent for nonempty root systems.
