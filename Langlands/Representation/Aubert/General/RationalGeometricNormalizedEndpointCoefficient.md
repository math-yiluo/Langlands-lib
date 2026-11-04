# Actual normalized geometric-term coefficient

This internal construction identifies the actual inducing coefficient of the
published geometric term with its ordinary Jacquet presentation. It then
compares the original normalized compact coefficient to that actual inducing
coefficient, retaining both original epsilon corrections.

## Literal objects and endpoint characters

Write `A = RationalPoint k G.X`, `MI = levi i ν I`, `MJ = levi i ν J`,
`UI = unipotent i ν I`, `UJ = unipotent i ν J`, and `PJ = parabolic i ν J`.
For the supplied actual normalizer element `n`, the groups used below are
literally

* `S = (MJ ∩ n⁻¹ UI n).subgroupOf MJ`;
* `Ls = (MJ ∩ n⁻¹ MI n).subgroupOf MJ`;
* `Lt = (MI ∩ n MJ n⁻¹).subgroupOf MI`;
* `K = (MI ∩ n PJ n⁻¹).subgroupOf MI`;
* `Rt = (MI ∩ n UJ n⁻¹).subgroupOf MI`.

Intersections and conjugate images here abbreviate the published
`geometricSourceIntersection` and `geometricTargetIntersection` definitions.
All `subgroupOf` restrictions are retained in Lean.
Let `π = hTarget.projection : K →* Lt` and let `e : Lt ≃* Ls` be the actual
inverse conjugation map, including the two nested-subgroup identifications.
The coefficient map is the original `p = geometricCoefficientLeviMap = e.comp π`.

The source character `χs` is
`geometricSourceEndpointInverseHalfCharacter`: the canonical closed inverse
Haar half of the actual radical `S` inside `MJ`, restricted to `Ls`.
The target character `χt` is the canonical closed positive Haar half of `Rt`
inside `MI`, defined on all of `K` with `hTarget.le_normalizer`.
Thus the full endpoint character is `χt * χs.comp p`.
Neither character is chosen freely.

## Actual geometric term before induction

For general closed subgroup families, `geometricTermInducingFunctor` is
the composite of the published `geometricSourceJacquetFunctor`, its original
`conjugationFunctor`, pullback along the actual target subgroup equivalence,
`inflationFunctor hTarget`, and the original target `inductionCharacter`
twist. Its codomain is `Rep ℂ K`; final raw smooth induction is omitted.
`geometricTermFunctor_eq_inducing` proves by reflexivity that composing with
`Induction.smoothInductionFunctor K` gives the published
`geometricTermFunctor`. The carrier universe of that equality is its original
`max uG uV`.

In the rational specialization, `geometricTermCoefficientTransport_eq`
proves that the composite of the source subgroup transport, inverse
conjugation, target subgroup transport and `π` is exactly `p`.
The proof uses `geometricIntersectionSubgroupEquiv_apply` and subtype
extensionality; it does not change the conjugation direction.

`geometricTermActualCoefficient σ` is the representation of this actual
inducing functor at a smooth representation `σ` of `MJ`.
`geometricTermOrdinaryEndpointCoefficient σ.representation` is

`twist χt ((twist χs (Jacquet.action σ.representation S Ls ...)).comp p)`

on the ordinary quotient `Jacquet.Coinvariants σ.representation S`.
`geometricTermOrdinaryEndpointCoefficient_eq` combines pullback of twists
and multiplication of twists to identify this with the twist by the full
endpoint character.

`geometricTermActualCoefficientEquiv` identifies the actual inducing
representation with this ordinary presentation. Its linear equivalence is
exactly `Jacquet.Localization.trivialEquiv.toLinearEquiv`.
For equivariance, a private generic pullback construction keeps that linear
equivalence, uses the proved equality of transport maps, and applies
`twistEquiv` for the two actual endpoint characters.
The forward map sends `Jacquet.Localization.mk σ.representation S 1 v`
to `Jacquet.mk σ.representation S v`; the inverse sends the ordinary class
back to that trivial-localization class. Both formulas are definitional.

`geometricTermInducingFunctor_map_mk` proves that the actual functor map
sends the class of `v` to the class of `SmoothRep.hom a v`.
`geometricTermActualCoefficientEquiv_natural` is the corresponding
naturality equality with the original ordinary `Jacquet.map`.
It is proved on quotient generators using
`Jacquet.Localization.mk_surjective` and the displayed class formulas.

## Comparison retaining both epsilons

Let `ε = (geometricEpsilonOne * geometricEpsilonTwo).comp π`, with the
original closedness and decomposition arguments.
`geometricNormalizedCompactCoefficient_eq_epsilonOrdinaryEndpoints`
proves the equality of representations

`geometricNormalizedCompactCoefficient σ =`
`  twist ε (geometricTermOrdinaryEndpointCoefficient σ)`.

Its proof substitutes
`geometricNormalizedCompactCharacter_eq_epsilonEndpoints` and uses
`twist_twist`. This uses the exact character factorization on the whole
of `K`, rather than only its common Levi.

`geometricNormalizedCompactActualCoefficientEquiv` composes that
representation equality with the inverse of
`geometricTermActualCoefficientEquiv`, twisted by `ε`. Its target is
precisely `twist ε (geometricTermActualCoefficient σ)`.
It sends each original ordinary class to the same trivial-localization
class. The inverse formula and
`geometricNormalizedCompactActualCoefficientEquiv_natural` are proved
using the original quotient maps and actual inducing functor maps.
No epsilon is set equal to one.

## Hypotheses, universes and provenance

The generic functor has independent index, ambient-group and carrier
universes. The rational construction has independent field universe `u`
and representation universe `uV`, with no restriction between them.
It permits arbitrary actual `I`, `J` and normalizer element `n`; no minimum
representative, splitness, characteristic or positive-rank restriction is
added.

The initial equivalence requires the displayed actual source and target
semidirect decompositions, ambient locally compact nonarchimedean topology,
and the closed Levi and unipotent families `hM`, `hU`.
The epsilon comparison additionally retains closedness of the original
parabolics at `I`, `J`, `StandardCocharacterStatement`, connected reductivity,
maximal splitness of the actual torus, genericity of the cocharacter,
point-normalizer comparison, second countability, the compact-limit
property of `UJ`, and continuity of both original Levi projections.
These are the hypotheses of the reused full-intersection character
factorization.

This is an internal deduction from the actual definitions in
`GeometricK0Target`, the actual inside normalization in
`LeviJacquetNormalization` and `Parabolic`, the published
`Jacquet.Localization.trivialEquiv`, the pullback and twist identities, and
the full-intersection endpoint-character factorization in
`RationalGeometricNormalizedEndpointCharacter`. The latter factors the
original character through its two original epsilons using the
`RationalGeometricNormalizedCoefficientCharacter` and
`RationalGeometricNormalizedCoefficientInflation` helpers.
The implementation uses no geometric expansion, adjointness, cuspidal
support, character independence or classification theorem as proof
evidence. These are proof-body dependencies; the broad imported module
closure contains further representation infrastructure and is not a
claim to have proved or applied its theorem targets.

This unit does not prove epsilon cancellation on the whole common Levi,
the normalized compact-induction comparison with the full geometric term,
the proper graded comparison, the ordered filtration, or
`RationalGeometricK0ExpansionStatement`. Those remain obligations of the
host proof.
