# Full-order Rosati classification of the joint Harris action locus

This is an internal extension of `HarrisIntegralCMActionLocus`. It uses
published additivity of actual dual maps and the published finite-basis
criteria. It adds no literature assertion or existence axiom.

Fix the same universe-zero Harris data `D`, signature charts `C`, scheme
`S` over `Spec F`, abelian scheme `B/S`, original
`PolarizedFiniteLevel.DualWitness W`, named `Prerequisites P`, and actual
map `lam : B ⟶ W.dual P`. The order is the auxiliary integral Harris
left-action order. The fixed map need not satisfy a polarization
predicate. For every test `T : Over S`, its dual witness and map are
constructed as `W.pullback P T.hom` and the canonical `W.pullbackMap`
of `lam`.

`harrisIntegralActionFullRosatiCondition` imposes the actual Rosati
equation for every element of that order, on the original direct
pullback family `B_T`. For a quasi-separated test base,
`harrisIntegralActionFullRosatiCondition_iff` identifies this with the
existing finite-basis condition. The proof applies
`integralRosatiEquations_iff_basis` using
`relativeDualSchemeMapAdditivity` for `B_T` and its constructed dual
witness. Additivity is therefore a proved input, rather than a new
familywise assumption.

`harrisIntegralCMFullActionCondition` combines the full order equations
with the unchanged `HarrisTaylorCMRationalLieDeterminantCondition` for
the published rational extension of the integral action. Its suffix
`_iff` theorem identifies it with the previous basis conjunction on
quasi-separated tests. The determinant retains its normalized reflex
coefficient map and its quantification over all finite families and
actual finite Lie charts.

Canonical relative restriction preserves this full conjunction between
quasi-separated tests: convert to the basis conjunction, apply its
proved Rosati and determinant restriction results, and convert back.
Locally noetherian schemes are quasi-separated. Consequently
`harrisIntegralCMFullActionSubfunctor` defines the full conjunction on
the entire full locally noetherian test category over `S`, with no
reducedness, geometric-point or connectedness restriction.

`harrisIntegralCMActionBasisFullIso` is a natural isomorphism from the
previous restricted basis-condition functor to this full-order functor.
Each component keeps the actual integral action and changes only its
proof of the condition. Both functors use the same relative restriction
map, so naturality is definitional.

The geometric inputs remain exactly those of the previous locus:

- `S` is locally noetherian.
- `R/eR` represents the actual relative endomorphism functor of `B`
  on all locally noetherian tests over `S`. Its structural map is
  separated and locally of finite type.
- Over the resulting raw integral-action scheme `U`, `H/eH` represents
  actual relative Hom from `B_U` to its constructed dual on all locally
  noetherian tests over `U`. Its structural map is separated.
- All tensor, Picard, duality and base-change propositions packaged in
  `P` remain explicit assumptions.

The scheme used here is the existing `harrisIntegralCMActionLocus`.
This module changes its classification, not its defining equations or
its geometric construction. Its closed inclusion into `U`, local
finite type and separatedness over `S`, and local noetherianness are
the already proved properties of that same scheme.

For each locally noetherian test, the theorem
`harrisIntegralCMFullActionLocus_factors_iff` says that a raw classifying
map factors through this locus exactly when its actual direct-family
action satisfies the full conjunction. This follows by rewriting the
condition in the previous factorization criterion. Like that criterion,
it does not need separatedness of `H`.

`harrisIntegralCMFullActionLocusHomEquiv` gives unique actual
classification by composing the previous Hom equivalence with the
identity-on-actions subtype equivalence. Its `_apply` theorem retains
the literal formula: compose the classifying morphism with the closed
inclusion into `U`, and restrict the actual universal integral action.
`harrisIntegralCMFullActionLocusIso` composes the previous natural
classification with `harrisIntegralCMActionBasisFullIso`, proving
natural representability of the full-order subfunctor on the unchanged
full locally noetherian category.

The rational conclusions use the same derived additivity.
`harrisIntegralCMFullActionCondition_involutionCompatible` applies
`rationalAction_involutionCompatible_of_integralBasis` after converting
the full conjunction to the basis conjunction. Thus the published
rational action is compatible with the positive auxiliary involution
and the rationalization of the actual pulled-back `lam`; the unchanged
determinant condition also holds.
`harrisIntegralCMFullActionCondition_rationalUnitMultiple` applies the
published homogeneity equivalence to every `q : ℚˣ`, proving involution
compatibility for the corresponding rational-unit multiple of that
map. Finally the Hom-equivalence theorem with suffix
`_involutionCompatible` supplies the rational involution and determinant
for every actual classifying morphism.

These are consequences for rationalizations of actual integral actions
and actual maps. No converse from rational equations to integral
equations, or integral lift of an arbitrary rational action, is asserted.
Existence of `R`, `H` and the ordinary moduli ambient scheme, the
normalized rational-isogeny and adelic-level comparison, admissibility
for every family on each output component, smoothness and division-case
projectivity remain obligations of
`DivisionCMRepresentabilityStatement`. A dual witness for the fixed
universal family does not supply universal output-component dual
geometry.
