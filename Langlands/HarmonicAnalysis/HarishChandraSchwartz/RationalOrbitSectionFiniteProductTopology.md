# Finite-product topology targets on actual rational orbit sections

This module specializes the finite-product constructions of
`OrbitSectionFiniteProductTopology` to the actual standard-parabolic data of
`rationalInducedOrbitSectionSpace`. The principal comparison remains an
unproved proposition. Fixed-coefficient finiteness is proved by an adapter of
published results.

The source is Waldspurger, *La formule de Plancherel pour les groupes p-adiques*,
VI.1, printed pp.295–296, and VI.3, printed p.301 (registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`;
PDF pp.61–62 and 67). The rational-point specialization, ordered-derivative
seminorm formulation and finite-basis coordinate implementation are internal
constructions of that description.

## Actual data and fixed coefficients

All declarations below are in `Langlands.HarishChandraSchwartz`. The field
`F : Type u` is any nonarchimedean local field, with no characteristic
restriction. The group scheme `G` is affine and locally of finite type over
`F`, with `hG : IsConnectedReductive G`. The actual structural data are a
maximal split torus `i`, a generic cocharacter `ν`, a finite subset `I` of
the corresponding simple roots, and a compact open subgroup `K` satisfying
the Iwasawa-pair condition with the minimal standard parabolic. The inducing
object `π` is an irreducible admissible complex smooth representation of the
literal standard Levi subgroup of `G(F)`. Its carrier universe `uV` is
independent of `u`; the group need not be split. No matrix representation,
measure normalization, temperedness or analytic estimate is retained from
the broader Fourier-continuity module.

`rationalOrbitSectionFixedCoefficients` abbreviates
`orbitSectionFixedCoefficients` at the actual standard semidirect
decomposition, `K` and `π`. For open `H ≤ K` it is precisely the
`H × H` fixed submodule of the existing
`ProductInducedCompactPicture`, using `π.obj` and its smooth contragredient.
It retains the original compact-picture representation.

`finiteDimensional_rationalOrbitSectionFixedCoefficients` proves its finite
dimensionality for every such `H`. It applies
`finiteDimensional_orbitSectionFixedCoefficients` with `hKc` and the
published `compactOpenCofinal_standardLevi I hKc`. The latter supplies the
needed Levi cofinality from `K ∩ M_I(F)`; it is not an additional premise.
The generic adapter derives product admissibility from irreducible
admissibility of `π`, published smooth-contragredient admissibility and
binary external-tensor admissibility. No admissibility of induction or
finiteness of the desired fixed space is assumed.

The three local instances named
`instRationalOrbitSectionFiniteProductTopology1`,
`instRationalOrbitSectionFiniteProductTopology2` and
`instRationalOrbitSectionFiniteProductTopology3` supply respectively the
standard Levi scheme's closed immersion, affineness and rational-point
topology. They use the same published structural results and topology as
`RationalFourierOrbitContinuity`.

## Level and total comparison targets

The full target
`Langlands.HarishChandraSchwartz.RationalOrbitSectionLevelFiniteProductTopologyStatement`
specializes `OrbitSectionLevelFiniteProductTopologyStatement` to the actual
standard parabolic, closed unipotent subgroup, closed parabolic, continuous
projection, `G(F) = P_I(F) K`, actual Levi norm characters and the canonical
`leviRationalUnitaryCoordinates`. It accepts an open `H ≤ K` and any finite
basis of its actual fixed coefficient space. No continuity premise on a
generic coordinate equivalence occurs.

The underlying level map is exactly `orbitSectionLevelCoordinates` at these
data. It composes the injective actual compact-restriction tensor map
`orbitSectionLevelTensor` with `smoothTensorCoordinates`. The imported
`orbitSectionLevelTensor_evaluation` recovers the original
`productInducedSmoothOrbitCompactRestriction` at every torus point.
The imported `orbitSectionLevelCoordinates_apply` says its coordinate `j`
is `b.coord j` of `orbitSectionLevelFixedRestriction` at that point.
The latter is the same compact restriction with values restricted to the
fixed submodule. `orbitSectionLevelCoordinates_injective` proves that
these coordinates distinguish actual sections.

The independent scalar topology uses the supremum norms of all ordered
angle derivatives, including the empty list for order zero. All finite
derivative orders occur, implementing the usual all-order smooth topology
in these coordinates. Derivative permutation is a separate optional target
in `SmoothTorusTensorTopology`; it is not assumed here. A finite coefficient
basis identifies the algebraic scalar-smooth tensor with a finite product of
these scalar spaces. The level target equates the existing topology with
the topology induced by the actual map into that product. The separate
`Langlands.HarishChandraSchwartz.SmoothTensorBasisIndependenceStatement`
compares different bases on the common tensor space.

`rationalOrbitSectionFiniteProductTopology` has type
`TopologicalSpace (rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π)`.
Given the family `d` of actual fixed-space finiteness witnesses, it
specializes the independent generic inductive-limit construction. The
underlying type agrees definitionally with that actual rational space.
Each chosen finite basis is `Module.finBasis` for the corresponding
witness in `d`. The construction takes the supremum of topologies
coinduced from those finite-product fixed levels through the existing
`OrbitSectionSpace.ofLevel` maps, then the infimum of all coarser
topological vector-space topologies locally convex over the reals, exactly
as in the existing `OrbitSectionSpace` convention. Its local convexity and
topological-vector-space properties are supplied by
`orbitSectionFiniteProductTopology_locallyConvex`.

The full target
`Langlands.HarishChandraSchwartz.RationalOrbitSectionTotalFiniteProductTopologyStatement`
equates the existing topology instance on that same actual rational section
space with this independent topology. The new topology is an explicit value
and is not installed as a global instance.

The principal full target
`Langlands.HarishChandraSchwartz.RationalOrbitSectionFiniteProductTopologyStatement`
existentially concludes a finiteness-witness family `d` for every open
`H ≤ K`. It then concludes the level comparison for every finite basis and
the total comparison using `d`. The finite basis index universe `uB` is
independent of the field and representation universes. Its hypotheses are
only the actual structural data above: finiteness, product admissibility,
induced admissibility, basis independence and topology comparisons are not
premises. The finiteness part already follows from the proved adapter; the
level and total equalities remain open.

## Correspondence and scope

VI.1 describes the compact restriction and actual self-twist covariance.
The source of each level map remains the existing `OrbitSectionLevel`;
the total space remains `rationalInducedOrbitSectionSpace`, whose elements
are the actual smooth induced orbit sections. The targets do not replace
these sections with arbitrary coefficient families or assert surjectivity
onto the ambient tensor. VI.3's finite-dimensional fixed coefficient
space gives the finite-product ambient topology; the actual fixed section
level inherits its subspace topology. The total topology follows the
locally convex inductive-limit convention of the Library. No completed
tensor product is used.

This module states the actual-point comparisons and proves only the
fixed-coefficient finiteness adapter. It does not prove topology equality,
wave-packet Schwartz membership or synthesis continuity.
