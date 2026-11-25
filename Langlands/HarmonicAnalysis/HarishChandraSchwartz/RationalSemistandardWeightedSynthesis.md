# Actual finite-support weighted semistandard synthesis

This construction and statement module belongs to the weighted synthesis of
Waldspurger's invariant spectral families.
Its principal target is
`Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis.SchwartzSynthesisStatement`.
It constructs the actual weighted raw synthesis, proves its linear and finite-
support formulas, states its remaining Schwartz and continuity properties,
and gives a conditional lift of that same raw map. Invariant restriction
and VI.3.2 factorization require the separate invariant subspace and projector
construction.

The original source is J.-L. Waldspurger (2003), *La formule de Plancherel
pour les groupes p-adiques*, registered as `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
VI.3, printed page 305 (PDF page 71), defines the full direct sum and its
weighted synthesis; Proposition VI.3.1, printed pages 302–305 (PDF pages
68–71), supplies the component Schwartz and continuity conclusions.
The finite-total utility and the implication from component lifts to global
membership are internal algebraic assembly of these actual source objects.

The field has arbitrary characteristic and universe `u`. Representation
carriers have independent universe `uV`. The ambient group scheme is affine,
locally of finite type and connected reductive, with the canonical point
topology. Maximal splitness and genericity enter the analytic targets
explicitly. There is no ambient splitness or quasi-splitness requirement,
no representation-carrier topology, and no positive-rank restriction.

## Actual input data

The published full family uses its intrinsic all-test indices, fixed
`chosenLeviModel`, actual split-component morphisms `a`, proofs `ha`, quotient
Haar measures `mu`, and `CompactData d`. The source-measure adapter additionally
retains affine split-component schemes, normal intrinsic split-center images,
and Borel literal quotients. Affineness and normality are the usual properties
of these actual central split tori, not new arbitrary groups or scalar data.
The actual finite-index premise on `RenardCartan.splitValuationImage (a t)`
is displayed for every parabolic index. This remains a structural obligation.
An actual `CocharacterPresentation hG t` is displayed for every intrinsic
index; the preceding conditional constructor uses exactly the published
`SemistandardSpectralDynamicCoverageStatement` for its existence.

`RationalSemistandard.OrbitPacketData r pi` packages only the exact primitive
inputs already required by the actual conditional density. Its fields are:

- `RelativeRootReflectionExistenceStatement` and
  `CentralSplitTorusCharacterStatement` witnesses;
- a scalar compact with compactness and both actual parabolic factorizations;
- `ForwardContinuation` and `ReverseContinuation` of the actual operators;
- open nonempty convergence domains with containment in the actual full
  domains, and an open nonempty generic irreducibility domain;
- `RationalFunctionUnitaryRegular` of the inverse actual
  `conditionalCanonicalRationalScalar` at all unitary parameters.

There is no coefficient, packet, Schwartz, form, invariant-stability or
averaging property among its fields. The generic irreducibility input does
not assume irreducibility of every tempered parabolic induction. The scalar
inputs are not proved here. `OrbitPacketData.packetLinear` calls the
previously constructed and proved `SourcePacket.rawWavePacketLinear` with
these exact fields. It selects no output map or analytic witness.

The family `Q` gives these primitive scalar inputs for every actual theta,
using precisely the actual `orbitRepresentative` and its published square-
integrability proof. Thus `GlobalSynthesis.componentPacket` is the actual
source-normalized packet at every full-family component, with no free
component maps.

## The actual weighted sum

`sourceWeight` is exactly `SourceConstants.unquotientedWeight` at the
parabolic's actual cocharacter presentation and displayed common compact
`K0`. Its real value is

```text
(c(G|M)^2)^(-1) * gamma(G|M)^(-1)
  * |W^M| / (|W^G| * |P(M)|).
```

All constants and cardinalities are the actual source constructions.
Their positivity theorem, from the source-constants module
`RationalSemistandardSourceConstants`, uses published source Haar/finite-product
proofs and the exact `SemistandardSpectralFiberFinitenessStatement` (proved as
`semistandardSpectralFiberFiniteness`). It does not take an arbitrary
positive scalar or supplied natural cardinalities.

`FiniteSupportSections.totalLinear` is a generic algebraic utility in this
pair. For linear maps from the actual component submodules, a summand
vanishes whenever the input component vanishes. Its support is therefore
contained in the input's literal finite support. The resulting finsum is
finite, its value is exactly the sum over that support, and its linear laws
follow from finite-support finsum additivity and scalar multiplication.
It imposes no finiteness on all geometric or spectral indices.

`GlobalSynthesis.weightedSynthesis` applies that proved utility to
`sourceWeight * componentPacket`. It is a complex-linear map from precisely
`rationalSemistandardThetaSmoothSections` to actual functions on `G(F)`.
`weightedSynthesis_eq_sum` gives equality of functions and
`weightedSynthesis_apply` gives the pointwise formula. These use the input's
finite support before any association or Weyl quotient. A summand can vanish
even when its input component is nonzero; no Fourier-support claim follows.
Pointwise integrability of every component packet has already been proved
in `RationalSemistandardWavePacket`.

## Exact remaining targets and conditional lift

`ComponentTopologicalSpace` is precisely the existing `OrbitSectionSpace`
for that component's actual norm characters, model coordinates, subgroup
decomposition and compact data. `componentToSmooth` is the published
identity-on-sections linear map. No new topology is declared. The separate
comparison with the source finite-dimensional tensor-product topology is
the statement `OrbitSectionFiniteProductTopologyStatement`
(`OrbitSectionFiniteProductTopology`).

The analytic targets explicitly retain actual maximal splitness, a generic
positive system, the existing
`BruhatTits.SpecialCompact.SpecialCompactProperties` predicate for `K0`,
and equality of every coefficient compact and every scalar compact with
that same source compact. These are concrete normalization compatibilities,
not assumptions of Schwartz membership or continuity. The raw sum is defined
without them. General comparisons with other compact pictures, models and
representatives are additional obligations; this module makes no
unconditional choice-independence claim.

`SchwartzMembershipStatement` concludes that the exact already constructed
raw sum lies in the existing `schwartzSubmodule` for every input family.
It also retains the precise geometric parabolic-fiber-finiteness target.
It assumes no global closure, Schwartz-valued map or estimate.
`ComponentContinuityStatement` concludes that each actual component packet
has a continuous complex-linear lift from its existing orbit-section topology
to the existing `RationalSchwartzSpace`, with exactly the same integral
values at every group point. It assumes no such lift or continuity property.
The source estimates for standard Levis are the standard-Levi statements of
`StandardLeviPlancherelWavePacketSchwartz`; the semistandard transport of their
conclusions is not proved here.

`schwartzMembership_of_componentContinuity` proves the routine global
assembly. For each contributing component, use the target's exact evaluation
formula to identify the raw packet with an element of the existing Schwartz
submodule. Scalar multiplication and the finite sum stay in that submodule.
This proves a conditional implication, not a new analytic estimate.
`SchwartzSynthesisStatement` is the joint Prop-valued target for the actual
global membership and actual component continuity conclusions.

`schwartzSynthesis` is conditional on `SchwartzMembershipStatement` and its
displayed source hypotheses. It restricts the codomain of the already
constructed `weightedSynthesis` by `LinearMap.codRestrict`.
`schwartzSynthesis_apply` proves that its values are exactly the raw weighted
sum. No arbitrary Schwartz-valued synthesis witness replaces the actual
construction.

## Dependency boundaries

Full indexing, actual fibers, smooth compact/model comparison and geometric
coverage/finiteness belong to the semistandard spectral families
(`RationalSemistandardSpectralFamily`, `RationalSemistandardOrbitSections`).
The particular all-unitary normalized comparisons belong to the normalized
Weyl/intertwiner comparisons of V.3; they are needed for invariant restriction
and factorization. Standard actual-source VI.3.1 estimates and continuous
synthesis belong to `StandardLeviPlancherelWavePacketSchwartz`. The scalar,
density and source-topology inputs and the conditional finite-length standard
intertwining theorem are not changed here. The common-Levi source-constant independence target
is not asserted as proved here.

The present module does not complete invariant kappa, VI.3.2 factorization,
source formal-degree transport, complete representative/model comparisons,
the global Hermitian form or association formulas. It proves no VII.2.5
isometry or VIII Fourier-family finiteness, surjectivity or inversion.
