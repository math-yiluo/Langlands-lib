# Conditional actual opposite standard integrals at the common source Haar scale

This module constructs the two actual opposite standard-integral families from
one cocharacter and one ambient compact open subgroup. Its provenance is
internal composition of published interfaces, rather than a new translation of
a numbered source theorem. The families and their integral specifications are
conditional on the two structural statements displayed below. Initial
convergence and rational continuation remain separate obligations.

The field `F` is an arbitrary nonarchimedean local field, including positive
characteristic. The ambient group scheme `G` has affine structure morphism and
is locally of finite type. The representation carrier has its own universe
`uV`, independent of the field and point-group universe `u`. No split or
quasisplit condition is imposed.

For the cocharacter `χ`, write `P`, `M` and `U` for its literal dynamic
parabolic, centralizer and contracted radical on the identity test scheme.
Write `Pbar` and `Ubar` for the dynamic parabolic and radical of the inverse
cocharacter. These are the declarations `parabolic`, `levi`, `radical`,
`oppositeParabolic` and `oppositeRadical`. `decomposition` is the actual
semidirect decomposition of `P`. `oppositeDecomposition` rewrites the published
inverse-cocharacter centralizer equality, so its Levi is exactly `M`.
`radical_isClosed`, `oppositeRadical_isClosed` and `levi_isClosed` use the
published rational-point closedness results in the canonical point topology.
The ambient topological-group, Hausdorff, local compactness and
nonarchimedean-group instances are also proved published rational-point facts.

`parameterScheme` is the actual affine scheme representing the dynamic
centralizer. `parameterHomeomorph` identifies its rational points
multiplicatively and topologically with the literal subgroup `M`, using
`dynamicCentralizerPointHomeomorph`.
`parameterScheme_isConnectedReductive` derives its connected reductivity from
`IsConnectedReductive G` by `dynamicCentralizerReductive`.
`normCharacters` consists of the actual rational-character norms
`(rationalNormCharacters (parameterScheme χ) ψ).toMul`.
`leviNormCharacters` transports them to `M` through that homeomorphism, and
`parameterTransport` is the induced homeomorphism of continuous unramified
character groups. Both integral directions use this identical parameter group
and character transport.

`radical_inf_oppositeRadical` proves `U ⊓ Ubar = ⊥`: an element of `U`
belongs to `P`, and the published all-test opposite unipotent/parabolic
intersection theorem then makes an element of `Ubar` equal to one.
Conjugation on a trivial subgroup is the identity, so its closed Haar
restriction character is one. The published opposite Haar reciprocity theorem,
`RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`,
therefore gives `conditionalSquaredModulus` and
`conditionalReverseSquaredModulus`. They retain precisely
`RelativeRootReflectionExistenceStatement.{u}` and
`CentralSplitTorusCharacterStatement.{u}`, as well as
`IsConnectedReductive G`. The actual dynamic centralizer reductivity needed by
that reciprocity route is already proved. No arbitrary squared-modulus
compatibility premise is supplied by a caller.

Fix an actual compact open subgroup `K` of `G(F)` with its compactness proof.
All radical, intersection and quotient measurable spaces used by the following
definitions are their canonical Borel spaces. `radicalHaar` and
`oppositeRadicalHaar` abbreviate `Haar.subgroupCompactOpenHaar`; each is intrinsic
Haar measure on its own radical, normalized by the inverse image of `K` having
mass one. `forwardIntersectionHaar` and `reverseIntersectionHaar` are the
corresponding `sourceIntersectionHaar` measures on `U.subgroupOf Ubar` and
`Ubar.subgroupOf U`, using the double-forgetful inclusion into the original
ambient group. Their Haar and regularity instances are inherited from the
published constructors.

The private `radicalCover` applies the published
`exists_compactOpenSubgroup` to a singleton in a dynamic radical. Hence every
radical element lies in a genuine compact open subgroup. The four exported
right-invariance instances apply
`sourceSubgroupHaar_rightInvariant_of_cover` or
`sourceIntersectionHaar_rightInvariant_of_cover` to these covers. In particular,
right invariance of the exact intrinsic source measures is proved here.

`forwardQuotientMeasure` is exactly
`DynamicSource.quotientMeasure K hK χ (Dynamic.inverseCocharacter χ)` on
`(U ∩ Ubar) \ Ubar`, expressed by `StandardIntertwining.QuotientSpace`.
`reverseQuotientMeasure` uses the cocharacters in reverse order and the same
`K`. These are the published selectors from proved existence of a compatible
quotient measure, fixed before any integral witness is received. The two
`_isCompatible` lemmas give full complex Weil compatibility with the exact
radical and intersection measures just specified. Regularity is inherited from
`DynamicSource.quotientMeasure_regular`; the two `_ne_zero` lemmas prove that
the quotients are nonzero. The measures are not arbitrary parameters or
restrictions of an ambient Haar measure.

For a canonical `SmoothRep ℂ M` named `A`, `forwardFullDomainRegion` and
`reverseFullDomainRegion` specialize
`standardIntertwiningFullDomainRegion` to these literal opposite data. A
parameter belongs to the forward region exactly when the actual integral
domain in the `P`-normalized induction of its unramified twist is the entire
source space. In the reverse region, the source is the `Pbar` induction.
Thus every source vector has absolutely convergent scalar integrals against
every smooth-dual functional, represented in the original inducing carrier at
every ambient point. These definitions assert neither openness nor
nonemptiness, nor that the two regions intersect.

`conditionalForwardFamily` and `conditionalReverseFamily` specialize
`standardInductionIntertwinerFamily` on those respective full regions, supplying
the actual decompositions, closedness, Haar measures, right invariance,
quotient compatibility and conditional squared-modulus proofs above. Their
values are intertwining maps between the two actual normalized inductions of
the same twist of `A`. The respective `_spec` lemmas are
`StandardIntertwining.HasIntegral` relations at every source vector: evaluation
of the resulting induced section is the vector represented by the original
smooth-dual scalar integrals. They follow directly from
`standardInductionIntertwinerFamily_spec`.

This construction supplies no special-compact or Iwasawa factorization,
nonempty convergence region, rational continuation, generic induced
irreducibility, scalar extraction or independence under changes of cocharacter,
parabolic, compact subgroup or Haar normalization. The fixed `K` has not been
identified with a special compact in the source. No source-normalized scalar
`j`, density `mu`, nonvanishing, positivity or Plancherel theorem is claimed.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
