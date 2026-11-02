# The joint Rosati and determinant locus of actual integral Harris actions

This is an internal construction from the actual universal integral action,
the closed Rosati and determinant equation loci, and the canonical relative
pullback comparisons. It adds no literature assertion or existence axiom.

Fix the universe-zero Harris data `D`, signature charts `C`, a scheme `S`
over `Spec F`, an abelian scheme `B/S`, its
`PolarizedFiniteLevel.DualWitness W`, the named `Prerequisites P`, and an
actual map `lam : B ⟶ W.dual P`. A polarization predicate is not required
for this equation-locus construction. The integral order and its integer
basis are the published auxiliary left-action order associated to `D, C`.
The determinant is the unchanged
`HarrisTaylorCMRationalLieDeterminantCondition`, with the published rational
extension of this integral action.

For every `T : Over S`, `harrisIntegralActionRosatiCondition` imposes the
finite-basis integral Rosati equations on the actual direct family
`baseChange T.hom B`. The dual witness is constructed as `W.pullback P T.hom`,
and the map to that dual is the canonical `W.pullbackMap` of `lam`.
No dual witness for each test is supplied independently.

For an arbitrary morphism `f : T' ⟶ T`, the theorem
`harrisIntegralActionRosati_restrict_iff` compares this condition for
`relativeEndRestrict B f` with the basis equations on the successive
pullback. The actual relative comparison is equivariant for the two
integral actions. The relative dual-valued composition theorem identifies
the transported successive pullback of `lam` with its canonical direct
pullback. The proof unfolds the published `DualWitness` wrappers and
applies `integralRosatiBasisEquations_relativeComparison_iff`.
Ordinary Rosati base-change stability then proves
`harrisIntegralActionRosati_restrict`. Together with the determinant
restriction theorem this defines `harrisIntegralCMActionSubfunctor` on
all schemes over `S`.

For geometric representability of this subfunctor on locally noetherian
tests, the construction retains the following inputs:

- `S` is locally noetherian.
- `R : Over S` represents the actual relative endomorphism functor of
  `B` on the full locally noetherian test category, through the natural
  isomorphism `eR`. Its structural map is locally of finite type and
  separated.
- On the resulting actual integral-action scheme `U`, `H : Over U`
  represents the actual relative Hom functor from the universal family
  `B_U` to its constructed dual, through `eH` on the full locally
  noetherian test category over `U`. Its structural map is separated.
- The tensor, Picard, duality and polarization base-change propositions
  packaged by `P` remain explicit assumptions. This module does not prove
  these propositions.

Local noetherianness of `U` is derived from local finite type of `R/S`
and the finite integral-action equation construction. The actual universal
action is `relativeIntegralActionUniversal`, obtained by classifying the
identity of `U`. Its dual witness and `lam_U` are obtained from `W, lam`
by the published pullback constructions.

`harrisIntegralCMActionLocus` applies `integralCMEquationLocus` to this
actual universal action and composes its map to `U` with `U ⟶ S`.
The inclusion into `U` is a closed immersion. Consequently the resulting
scheme is separated and locally of finite type over `S`, and locally
noetherian. Closedness uses separatedness of `H/U`.

`harrisIntegralCMActionLocus_factors_iff` states that a classifying map
`T ⟶ U` from any locally noetherian test factors through this locus if
and only if its classified action on the original direct family `B_T`
satisfies both conditions. In the proof, `T` is also regarded as a test
over `U`. The joint equation-locus theorem gives the conditions on the
successive family. The Rosati restriction equivalence above identifies
the first with the direct-family condition. The determinant restriction
equivalence, the determinant pullback-class equivalence and compatibility
of rational extension with base change identify the second. A scheme
factorization is converted to a morphism over `S` using its structural
triangle. This factorization criterion itself needs no separatedness
assumption on `H`.

`harrisIntegralCMActionLocusHomEquiv` sends a morphism into the joint
locus to the raw action classified by its composite with the inclusion.
Surjectivity follows from the factorization criterion and the inverse raw
classification. Injectivity follows from raw classification and the
monomorphism of the closed inclusion. The theorem with suffix `_apply`
identifies this map literally with relative restriction of the actual
universal action.

Finally `harrisIntegralCMActionLocusIso` is the natural isomorphism between
the restricted lifted Yoneda functor of this scheme and the simultaneous
subfunctor, on the unchanged full locally noetherian category over `S`.
The components use the Hom equivalences and the standard `ULift` subtype
equivalence. Naturality is the composition law for canonical relative
restriction. No natural comparison is assumed as an extra input.

The Rosati predicate here is the finite-basis predicate. The all-order
Rosati equivalence and rational involution conclusion additionally require
the published dual-additivity input; this module does not assert those
conclusions. It also does not assert the existence of `R`, `H`, or an
ordinary moduli scheme. The normalized rational-isogeny and adelic-level
moduli comparison, admissibility, smoothness, and division-case projectivity
remain obligations of `DivisionCMRepresentabilityStatement`.
