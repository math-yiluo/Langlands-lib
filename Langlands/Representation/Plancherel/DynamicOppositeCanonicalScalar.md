# Conditional fixed-source scalar of the actual opposite standard integrals

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

At the beginning of IV.3, printed p.285 / PDF p.51, the composite of the
standard intertwining integrals for a parabolic and its opposite is a
scalar on the generic irreducibility locus, by Schur's lemma, and this
scalar is rational in the unramified parameter. This module is an
internal adapter, not a translation of a separately numbered assertion.
It instantiates the published fixed-data construction of
`StandardInductionCanonicalScalar` with the literal opposite data, the
intrinsic source Haar measures and the conditional standard families of
`DynamicOppositeStandardIntertwining`. Every declaration is a
specialization of a published result to those actual data, apart from the
small topology and unimodularity lemmas below and the composition proof of
`conditionalCanonicalRationalScalar_spec`.

The fraction defined here is the scalar for one fixed cocharacter, one
fixed compact open subgroup `K`, one inducing representation and the
`K`-normalized source measures. It is not identified with the function
`j` of IV.3. Waldspurger fixes a special maximal compact subgroup `K` and
the Haar measures with `mes(H ∩ K) = 1` once and for all in I.1, printed
p.240 / PDF p.6. With these conventions fixed, IV.3(1), printed
pp.285–286 / PDF pp.51–52, proves that `j_P` is independent of
`P ∈ P(M)`. The source asserts no independence of the Haar
normalizations, and none is claimed here.

## Actual data and proved premises

The field `F` is an arbitrary nonarchimedean local field, including
positive characteristic. The group scheme `G` has affine structure
morphism and is locally of finite type; no split or quasisplit condition
is imposed. The field and point-group universe `u` and the
representation-carrier universe `uV` are independent. For the cocharacter
`χ`, the notation `P`, `Pbar`, `M`, `U`, `Ubar`, `decomposition`,
`oppositeDecomposition`, `parameterScheme`, `parameterHomeomorph`,
`normCharacters`, `leviNormCharacters` and `parameterTransport` is that
of `DynamicOppositeStandardIntertwining`. In particular the two
decompositions have the same literal Levi subgroup `M`, and both
directions use the same parameter group of unramified characters of the
actual dynamic centralizer scheme.

The local instances put the canonical point topology on `G(F)`. The
published rational-point results make it a Hausdorff, locally compact,
nonarchimedean topological group, and second countable via
`Aubert.General.rationalPoint_secondCountableTopology`. The centralizer
inclusion is a closed immersion, by `Dynamic.Affine.isClosedSubgroup_centralizerHom`.
Hence the centralizer scheme is affine. It is locally of finite type
because its structure morphism equals the closed immersion followed by
the structure morphism of `G`. Its rational points get the canonical point
topology and the published nonarchimedean-group structure.

The following lemmas prove the analytic and normalization premises
required by the published constructor:

* `parameterProjection_continuous`: the valuation-image projection of the
  centralizer's rational points is continuous.
* `normCharacters_continuous`: every actual rational norm character of
  the centralizer is continuous.
* `parabolic_isClosed` and `oppositeParabolic_isClosed`: `P` and `Pbar`
  are closed in `G(F)`.
* `projection_continuous`: the semidirect projection `P → M` is
  continuous.
* `oppositeProjection_continuous`: the same for `Pbar → M`. The published
  continuity result has values in the Levi of the inverse cocharacter. A
  local transport lemma eliminates the published equality of that Levi
  with `M`.
* `radical_unimodular` and `oppositeRadical_unimodular`: given
  `IsConnectedReductive G`, `U` and `Ubar` satisfy `IsUnimodularModulus`.
  This is the published compact-containment result
  `DynamicNormalization.dynamicUnipotent_isUnimodular`.

The radicals, both subgroup intersections and both quotient spaces carry
their Borel structures, matching those of
`DynamicOppositeStandardIntertwining`.

## Remaining explicit inputs

The structural premises are `RelativeRootReflectionExistenceStatement.{u}`
and `CentralSplitTorusCharacterStatement.{u}`. They enter only through the
conditional squared-modulus identities `conditionalSquaredModulus` and
`conditionalReverseSquaredModulus`, and hence through the actual
families. `IsConnectedReductive G` is also explicit. Further explicit
inputs are a compact open subgroup `K` with compactness proof `hK`, both
factorizations `G(F) = P K` (`hPK`) and `G(F) = Pbar K` (`hOppK`), and a
canonical `SmoothRep.{0,u,uV} ℂ M` named `A`.

`conditionalForwardCompactFamily` and `conditionalReverseCompactFamily`
are the published `compactIntertwiningOperator` conjugates of
`conditionalForwardFamily` and `conditionalReverseFamily`. They are
defined on the exact full domains `forwardFullDomainRegion` and
`reverseFullDomainRegion`. Every member of a full domain requires absolute
convergence of every scalar integral and representability in the original
inducing carrier, for every source vector and every group element. Both
directions use the same `K` and the normalized restriction/extension
equivalences of the published compact picture.

`ForwardContinuation` and `ReverseContinuation` are the types of
`RationalOperatorContinuationData` for these two compact families. A term
of either type is a whole-operator rational continuation: an operator
numerator family, polynomial on all parameters, and a regular denominator
nonzero on the entire full domain, such that the numerator is the
denominator times the actual family at every point of the full domain.
These abbreviations assert no existence of a continuation.

The remaining inputs are:

* continuations `p` and `q`;
* a nonempty open `DForward` contained in the forward full domain, and a
  nonempty open `DReverse` contained in the reverse full domain;
* a nonempty open set `D` of parameters at which the actual normalized
  induction `UnramifiedLeviInduction` from `P` of the twisted `A` is
  irreducible.

The two convergence sets are independent. No intersection of `DForward`,
`DReverse` or the two full domains is assumed, and `D` need not avoid
any denominator. The definition of the fraction uses only nonemptiness,
the two inclusions and the irreducibility premise. Openness of the
convergence sets is an input of every later declaration except
`exists_normalized_compactCoefficient`; it enters the published continued
intertwiners in `conditionalContinuedComposite`.
Openness of `D` is an input of the locus-independence, extraction,
stabilizer, presentation and specification results and of both ambient
equations below. It is not used by `conditionalContinuedComposite` or
`exists_normalized_compactCoefficient`.

## The fraction and its independence

`conditionalCanonicalRationalScalar` is the published
`standardInductionCompositeCanonicalRationalScalar`, applied to
`L = parameterScheme χ`, its proved connected reductivity, the two actual
decompositions with the lemmas above, the actual source measures and
their Weil compatibilities, and the conditional squared-modulus
identities. It is an element of the published rational function field
`rationalUnramifiedFunctionField` on the unramified characters of the
centralizer. It is extracted from the reverse continued compact operator
after the forward one, at the normalized coefficient selected internally
from one point of `D`.

* `conditionalCanonicalRationalScalar_continuation_independent`: the
  fraction is unchanged when `p` and `q` are replaced by any other
  continuations `p'` and `q'` of the same families. This uses openness of
  the convergence sets but not of `D`, and needs no scalarity.
* `conditionalCanonicalRationalScalar_irreducibility_locus_independent`:
  replacing `D` by any nonempty locus `D'` of the same actual
  irreducibility gives the same fraction. Only `D` is required to be
  open.
* `conditionalCanonicalRationalScalar_eq_extraction`: for every compact
  vector `v` and algebraic linear functional `ℓ` with `ℓ v = 1`, the
  fraction equals `continuedCompositeRationalScalar p q v ℓ`.
* `conditionalCanonicalRationalScalar_stabilizer_fixed`: for every
  element `τ` of the full stabilizer of the isomorphism class of
  `π = SmoothRep.pullback (parameterHomeomorph χ) A` under unramified
  self-twists, translation by `τ` fixes the fraction. Finiteness of the
  stabilizer is not assumed.
* `conditionalCanonicalOrbitScalarPresentation`: under an explicit
  `Finite` instance for that stabilizer, this is the published
  `UnramifiedInvariantScalarPresentation` of exactly this fraction.

The published results specialized by the locus-independence,
extraction, stabilizer, presentation and specification results, and by
both ambient equations below, assume a separable ambient group.
Separability of `G(F)` is supplied here by the proved second
countability, not assumed.

## The actual composite and its scalar

Write `R = p.regularRegion ∩ q.regularRegion`, the common regular region
of the two continuations. `conditionalContinuedComposite` is the
published `continuedInductionComposite` on `R`: the reverse actual
continued intertwiner after the forward one, as an endomorphism of the
actual normalized induction from `P` at each parameter of `R`.

`conditionalContinuedCompositeRationalScalar_spec` specializes
`continuedInductionCompositeRationalScalar_spec` to every normalized
coefficient `(v, ℓ)`. It gives regular functions `a`, `b` with `b ≠ 0`
and `b` nonzero at every point of `R`. The coefficient fraction
`continuedCompositeRationalScalar p q v ℓ` equals `a / b`, and for every
`z` in `R` the continued composite is `(a z / b z)` times the identity.

`exists_normalized_compactCoefficient` proves that the actual compact
carrier has some `(v, ℓ)` with `ℓ v = 1`. It applies the published
`compactInductionScalarExtraction` at a point chosen from the nonempty
set `D`, using the irreducibility premise there.

`conditionalCanonicalRationalScalar_spec` states the same regular
presentation directly for `conditionalCanonicalRationalScalar`. Write
`J^ext_{Pbar|P}` for the forward continued intertwiner, from the
`P`-induction to the `Pbar`-induction, and `J^ext_{P|Pbar}` for the
reverse one. There are regular `a` and `b` with `b ≠ 0` and `b` nonzero
throughout `R`, such that the fraction is `a / b` and, for every `z` in
`R`,

\[
J^{\mathrm{ext}}_{P|\bar P}(z)\,J^{\mathrm{ext}}_{\bar P|P}(z)
  = \frac{a(z)}{b(z)}\,\mathrm{id}.
\]

Its proof takes the coefficient of `exists_normalized_compactCoefficient`,
applies `conditionalContinuedCompositeRationalScalar_spec` to it and
rewrites the fraction by `conditionalCanonicalRationalScalar_eq_extraction`
through transitivity of equality. The theorem needs no finiteness of the
stabilizer and no irreducibility at the evaluation parameter; reducible
parameters of `R` are included.

For any invariant presentation `r` of the fraction:

* `conditionalContinuedComposite_eq_canonicalOrbitScalar`: at every `z` in
  `R` where the denominator of `r` is nonzero, the continued composite
  equals the orbit value of `r` at the twist class of `π` by `z`, times the
  identity.
* `conditionalOriginalComposite_eq_canonicalOrbitScalar`: at every `z` in
  the intersection of the two original full domains where that
  denominator is nonzero, the composite of the original reverse and
  forward families equals the same multiple of the identity. Nonemptiness
  of this intersection is not asserted.

These are equalities of ambient `Representation.IntertwiningMap` objects.

## Boundaries

The module proves no initial convergence, nonempty open full-domain
subset, whole-operator rational continuation, generic irreducibility or
finiteness of the self-twist stabilizer. Neither factorization of `G(F)`
is proved. Nor are the root-reflection and central split-torus
statements. Nothing identifies `K` with a special maximal compact
subgroup of the source.

No independence of the parabolic subgroup, cocharacter, `K`, Haar
normalization, compact model or inducing representative is claimed. No
source-normalized `j`, nonvanishing, positivity, density `mu`, or
Plancherel conclusion is claimed.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
