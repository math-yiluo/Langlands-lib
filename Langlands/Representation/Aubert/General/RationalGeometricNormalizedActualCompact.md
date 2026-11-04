# The actual normalized geometric coefficient under compact induction

This internal construction lifts the actual normalized inducing-coefficient
comparison through compact induction and composes it with the original
normalized compact comparison. Both original epsilon corrections remain.
The final exact-K0 expansion and cancellation of these corrections remain
separate proof obligations.

The literal target intersection K is the subgroupOf copy of
M_I intersect n P_J n⁻¹ inside M_I. The character used here is the product of
the original `geometricEpsilonOne` and `geometricEpsilonTwo` on the literal
common Levi, composed with the original target-intersection Levi projection.
The source radical S and common Levi Ls remain the subgroupOf copies of
M_J intersect n⁻¹ U_I n and M_J intersect n⁻¹ M_I n inside M_J.
All normalizer representatives n and both standard subsets I,J are arbitrary.

`isOpen_ker_geometricInflatedEpsilonProduct` first includes the intersection
of the two original open kernels in the product's kernel and uses
`Subgroup.isOpen_mono`. Pulling back this open set along the actual Levi
projection proves the result on all K. The required continuity is exactly
`continuous_geometricTargetProjection`, derived from continuity of the
original P_J projection and the given target semidirect decomposition.
`geometricInflatedEpsilonProductSmoothCharacter` packages this same character
and its proved open kernel. No new projection-continuity premise is introduced.

`geometricTermEpsilonCompactFunctor` is the composite of
`geometricTermInducingFunctor`, this epsilon character's `twistFunctor`, and
the actual `compactInductionFunctor K`. It uses their existing morphisms and
functor laws. Thus it retains the original source normalized Jacquet functor,
conjugation action x ↦ sigma(n⁻¹ x n), target Levi inflation and target positive
half before applying the two epsilon factors and compact induction.

`geometricNormalizedCompactActualTargetIso` is `SmoothRep.mkIso` applied to
`compactInducedEquiv K` of `geometricNormalizedCompactActualCoefficientEquiv`.
Its evaluation formula, `geometricNormalizedCompactActualTargetIso_eval`,
is exactly the original coefficient equivalence on each original function
value. It therefore preserves the original ordinary Jacquet class as the
corresponding trivial-localization class. No support or integral comparison
is replaced. `geometricNormalizedCompactActualTargetNatIso` uses these
components in `NatIso.ofComponents`. Morphism and compact-function
extensionality reduce its naturality square to
`geometricNormalizedCompactActualCoefficientEquiv_natural` at each value.

`geometricNormalizedCompactActualNatIso` composes the published
`geometricNormalizedCompactNatIso` with this target natural isomorphism.
Its source is exactly `geometricNormalizedCompactSourceFunctor`, the original
normalized compact orbit quotient. Its target is the compact functor just
defined, including both epsilon factors. The component map first applies the
published original quotient-integral comparison and then the pointwise
coefficient equivalence above.

The input category is `SmoothRep.{0,u,uV} ℂ M_J` and the output category is
`SmoothRep.{0,u,max u uV} ℂ M_I`; the field and coefficient-carrier universes
are independent. The final natural isomorphism retains ambient local
compactness, nonarchimedean structure, Hausdorffness and second countability;
closedness of every actual Levi and unipotent subgroup and of P_I and P_J;
continuity of the original two Levi projections; the limit-of-compact-subgroups
properties of U_I and U_J; connected reductivity, the original maximal split
torus and generic cocharacter; the standard-cocharacter and point-normalizer
comparison hypotheses; and the original source and target intersection
semidirect decompositions. Its prerequisites carry the smaller scopes visible
in their Lean declarations. There is no characteristic, splitting, rank,
subset or normalizer-representative restriction.

The provenance is internal functor assembly from the named imported coefficient
and compact comparisons. The proof bodies use their existing equivalences and
naturality, the original epsilon open-kernel lemmas, actual projection
continuity, open subgroups, extensionality and categorical composition.
They introduce no geometric-expansion, adjointness, cuspidal-support,
character-independence or classification premise. These are proof-body
dependencies; the imported-module closure is larger. Whole-common-Levi
distinct-radical balance, epsilon cancellation, compact/full induction,
the proper graded comparison, ordered filtration and final exact-K0 expansion
remain separate obligations.
