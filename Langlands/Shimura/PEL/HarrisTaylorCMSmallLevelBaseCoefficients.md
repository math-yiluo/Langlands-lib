# Base-sheaf coefficients on the actual small geometric CM tower

This is an internal construction from the actual geometric CM tower and the
restricted canonical-coefficient API. All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. It constructs coefficients
from sheaves on the geometric base, proves their level triviality, and gives
smooth shrinking-level cohomology and section functors. It supplies no
unconstrained tower of schemes or coefficient transitions.

## Actual geometric input

The arithmetic data, CM section and signature charts `D` and `C`, rational
profinite-integer/adele comparison `h`, tensor comparison and coherence,
Picard, duality, polarization, Weil-transition and torsion premises are
exactly those of `HarrisTaylorCMSmallLevelCohomology`. The proposition `q`
is the existing `CMRepresentabilityStatement` for the fixed CM moduli
presheaves, with their smooth and projective representation witnesses. It is
retained as an assumption, not replaced by a collection of arbitrary schemes.
All scheme and coefficient universes in this specialization are zero.

Write `G` for `D.rationalInvolution.FiniteAdelicPoints` with its opposite
group structure. Write `T` for the existing `cmGeometricSchemeTower`, indexed
by `SmallCMLevel D`, and `B` for `Spec(AlgebraicClosure F)`. The tower is the
actual represented CM tower base changed from `Spec F` along the existing
`cmGeometricFieldMap`.

`cmSmallLevelGeometricStructure` constructs a natural transformation
`p : T ⟶ const B` from the structure morphisms of
`cmGeometricOverTower`. The component at `U` is exactly that object's morphism
to `B` (`cmSmallLevelGeometricStructure_app`), hence the second fiber-product
projection in the already constructed geometric tower. Naturality is proved
from the morphism law in the over category. In particular
`T.map k ≫ p_V = p_U` for the original transporter `k : U ⟶ V`
(`cmSmallLevelGeometricStructure_naturality`). These constructions require no
additional etaleness or rigidity premises.

The coefficient constructions additionally retain
`RelativeDualSchemeExistenceStatement`, `RelativeDualSchemeGeometryStatement`,
`CMGeometricCoarseRigidity` at every small CM level and the named
`DominantUnramifiedEtaleStatement`. The already constructed
`cmSmallLevelTowerEtale` derives etaleness of every original geometric
transporter from these precise hypotheses. Each definition installs this
proved result for coefficient restriction; it does not assume the desired
etaleness of an arbitrary scheme tower. The coefficient ring `R` is any
commutative ring in universe zero. The structure morphisms `p_U` themselves
are not assumed etale.

## Constructed coefficients and their triviality

For a module sheaf `M` on the small-etale site of `B`,
`cmSmallLevelBaseCoefficients M` is the genuine inverse-image coefficient
diagram on `T.op`. Its object at `op U` is
`(EtaleInverseImage.inverseImage p_U R).obj M`
(`cmSmallLevelBaseCoefficients_obj`). The existing inverse-image functor is
the constructed small-etale sheaf inverse image.

For an original transporter `k : U ⟶ V`, the transition at `k.op` is exactly
`LevelTowerCohomology.restrictionProjectionIso` for `p_V`, `p_U`, `T.map k`
and the proved naturality triangle, evaluated at `M`
(`cmSmallLevelBaseCoefficients_map`). The identity and composition coherence
are inherited from the actual generic canonical-coefficient construction
and its conversion from inverse image to restriction along etale maps; no
transition morphisms or coherence equalities are supplied as input.

`cmSmallLevelBaseCoefficients_trivial` proves the full sheaf-level
`cmSmallLevelTrivialCoefficients` property. The proof applies the published
canonical-coefficient congruence theorem to the actual scheme self-arrow
identity `cmGeometricSchemeTower_restrictedSelfArrow`. That identity fixes
`T(U)` for every subgroup element `k ∈ U`. Because these coefficient
transitions are constructed projection comparisons, equality of the scheme
arrows gives equality of the coefficient transitions after the specified
restriction comparison. No separate coefficient-triviality premise is
required for these particular coefficients.

`cmSmallLevelBaseCoefficientsFunctor` maps base sheaves into the full
subcategory of actual level-trivial CM coefficient diagrams. Its underlying
object is precisely the displayed coefficient diagram
(`cmSmallLevelBaseCoefficientsFunctor_obj`). On a morphism of base sheaves,
the component at each level is the actual inverse-image morphism along
`p_U` (`cmSmallLevelBaseCoefficientsFunctor_map_app`). Its functor laws and
compatibility with level transitions follow from the existing functorial
canonical-coefficient construction.

`cmSmallLevelBaseCoefficients_cohomology_obj` identifies degree `d`
cohomology at level `U` with ordinary small-etale cohomology
`H^d(T(U), p_U^* M)`, using the existing right-derived global-section functor.

## Smooth cohomology, sections and representatives

`cmSmallLevelBaseCohomologyFunctor d` sends `M` to the colimit of these
cohomology modules over shrinking inclusions of actual sufficiently small
CM levels, with its smooth `G` action. It is a functor in `M` to
`SmoothRep R G`. Its value is exactly the earlier
`cmSmallLevelSmoothCohomology` applied to `cmSmallLevelBaseCoefficients M`
and its proved triviality (`cmSmallLevelBaseCohomologyFunctor_obj`). The
colimit index is the opposite of the actual ordered small-level category;
the full transporter category supplies the action.

Finite dimension of `A` over the rationals is derived from `D.finite` and
`Module.Finite.trans F A`. Together with the previously proved actual
smallness instances, this supplies conjugation stability for the action
and downward closure for the representative theorem. These are not added
arithmetic finiteness premises. Smoothness uses the proved coefficient
triviality and the openness of each actual level subgroup.

`cmSmallLevelBaseSectionsFunctor` constructs the analogous smooth functor
from global sections of the same inverse-image coefficients.
`cmSmallLevelBaseCohomologyZeroIso` is a natural isomorphism from the degree
zero cohomology functor to this sections functor in the category of smooth
representations, reusing the established degree-zero comparison.

`cmSmallLevelBaseCohomology_action` states that `g` sends a class represented
at `U` to its pullback along the original geometric transporter from
`restrictedConj small g U` to `U`, followed by the constructed coefficient
comparison and insertion into the colimit at that conjugate level. The
conjugation and multiplication conventions are those of the same opposite
finite-adelic group. The formula specializes the generic canonical action
formula without changing the scheme map or the coefficient transition.

With the explicit additional assumption `Nonempty (SmallCMLevel D)`,
`cmSmallLevelBaseCohomology_exists_level` proves that every element of this
smooth cohomology module is represented by a cohomology class at one actual
small CM level. It uses the existing single-level representative theorem
and actual downward closure; it does not prove the existence of a small
level.

## Provenance and remaining obligations

This module makes no new assertion from external literature. Its provenance
is internal: the actual over-tower gives the structure transformation;
`HarrisTaylorCMSmallLevelCohomology` supplies the actual indices, derived
etaleness, self-arrow identity and cohomology adapter;
`RestrictedLevelTowerCanonicalCoefficients` supplies the constructed
inverse-image diagrams, their triviality, functors, comparisons and class
formulas. The generic construction is specialized to this exact CM tower
and its exact structure map, rather than an arbitrary supplied projection.

The representability proposition, named geometric prerequisites, arithmetic
existence and small-level nonemptiness remain assumptions where displayed.
These are coefficients pulled back from the geometric base. This module
does not identify the pullback of a constant sheaf with a separately defined
constant sheaf, assert local constancy for arbitrary `M`, or construct the
Harris coefficient systems arising from algebraic representations as
compatible diagrams over all small levels. Their nonconstant descent and
level-triviality proofs remain separate obligations. It also constructs no
Galois action, extension to nonsmall scheme levels, compact supports,
finiteness theorem, limit-scheme comparison, or unconditional canonical-model
or representability theorem. This is a focused progressive construction,
not completion of the broader Harris prerequisites.
