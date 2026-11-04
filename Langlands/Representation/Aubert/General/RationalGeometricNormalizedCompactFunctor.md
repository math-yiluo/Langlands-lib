# The actual normalized compact comparison as a natural isomorphism

This internal deduction packages the original normalized compact comparison as
a natural isomorphism of smooth representation functors. It uses precisely the
source, coefficient and target maps of
`RationalGeometricNormalizedCompactNaturality` and the smooth isomorphism of
`RationalGeometricNormalizedCompact`. The full rational geometric exact-K0
expansion remains open.

The notation and subgroups are those of the imported naturality module.
Q = P_I and L = M_I are the actual original standard subgroups. H is the literal
subgroupOf copy of P_I intersect n P_J n⁻¹ in P_I, and K is the literal
subgroupOf copy of M_I intersect n P_J n⁻¹ in M_I. The source radical S and
common Levi Ls are the subgroupOf copies of M_J intersect n⁻¹ U_I n and
M_J intersect n⁻¹ M_I n inside M_J. The original coefficient projection f,
common-Levi map p, Levi inclusion s and semidirect decompositions are retained.
Chi, kappa and eta are respectively the original positive U_J half-character,
original inverse U_I half-character and exact full-K coefficient character
`geometricNormalizedCompactCharacter`.

`geometricNormalizedCompactSourceMap_id` and
`geometricNormalizedCompactSourceMap_comp` prove the map laws on the original
target-radical coinvariant quotient. Intertwiner and linear-map extensionality
reduce them to quotient representatives. For identity, compact-function
extensionality gives the identical original function. For composition, the
representative formulas for the two original pointwise coefficient maps agree
definitionally. The chi and kappa twists leave these underlying linear maps
unchanged.

`geometricNormalizedCompactCoefficientMap_id` and
`geometricNormalizedCompactCoefficientMap_comp` prove the map laws on the
ordinary source Jacquet quotient with its eta-twisted action. Intertwiner and
linear-map extensionality followed by induction on the actual coinvariant
class reduce both claims to the same original vector class. The target-map
laws then use compact-function extensionality and evaluate those coefficient
map equalities at each original function value. Thus all six laws concern
the existing maps, including their original subgroup restrictions and
normalization characters.

`geometricNormalizedCompactSourceFunctor` sends a smooth representation A of
M_J to the original kappa twist of the target-radical coinvariants of
`compactInduced H ((twist chi A.representation).comp f)`, restricted along s.
Its smoothness proof is exactly
`isSmooth_geometricNormalizedCompactSource`. Its morphisms are the original
`geometricNormalizedCompactSourceMap`, and the two source-map laws above
give its functor laws through `SmoothRep.ofHom`.

`geometricNormalizedCompactTargetFunctor` sends A to compact induction from
K of the eta twist of its ordinary S Jacquet action pulled back along p.
Smoothness is `compactInduced_smooth`; morphisms are exactly
`geometricNormalizedCompactTargetMap`. The target-map laws give the functor
laws through `SmoothRep.ofHom`. No finite-length property is needed or
concluded for either functor.

`geometricNormalizedCompactNatIso` uses `NatIso.ofComponents` with components
exactly `geometricNormalizedCompactSmoothIso`. Morphism extensionality and
`geometricNormalizedCompactEquiv_natural` prove its naturality square. In
particular, the component map is the original quotient-integral comparison
with both endpoint half-characters and the remaining actual Haar correction;
no alternative comparison map or character identification is chosen here.

The field universe u and coefficient-carrier universe uV are independent.
The input category is `SmoothRep.{0,u,uV} ℂ M_J`, and the output category is
`SmoothRep.{0,u,max u uV} ℂ M_I`. The rational-point and subgroup carriers have
universe u; the compact-function carriers have universe max u uV.
The coefficient and source map laws also allow independent intermediate
carrier universes uW and uX. The source functor and natural isomorphism retain
ambient local compactness, nonarchimedean structure and Hausdorffness;
closedness of U_I, U_J, P_I, P_J, M_I and M_J; continuity of the original Levi
projections; the compact-limit property of U_I; connected reductivity; the
original maximal split torus and generic cocharacter; the standard-cocharacter
and point-normalizer comparison hypotheses; and the original source and
target decompositions. The target functor and all map laws have only the
smaller scopes needed by their actual definitions. There is no restriction
to characteristic zero, split groups, positive rank, particular I/J or
minimal normalizer representatives.

The provenance is internal functor packaging of the named published compact
comparison and original-map naturality results. The proof bodies use
coinvariant induction, extensionality, the original map definitions, the
existing smooth realization and naturality. They add no geometric expansion,
adjointness, cuspidal-support, character-independence or classification
premise. The imported-module closure is larger. Whole-common-Levi
distinct-radical balance, identification with the normalized geometric-term
coefficient, compact/full induction, proper graded comparisons, ordered
filtration and the final exact-K0 equality remain separate obligations.
