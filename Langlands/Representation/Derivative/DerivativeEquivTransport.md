# Transport of the derivatives along representation equivalences

Author: Worker 749.

This helper module shows the following. Let two smooth representations be
related by an actual equivalence of representations, where their carriers
may lie in different universes. Then their images under every published
derivative functor of `Langlands.Representation.Derivative.Iteration`, and
under each functor in its telescope, are again related by an actual
equivalence. It also shows that finite group-algebra length
(`SmoothRep.HasFiniteLength`) passes along such an equivalence.

The proof module `GeneralLinearDerivativeFiniteLengthProof` uses it once.
There the input `A` with carrier in `Type uV` is replaced by its universe lift
`SmoothRep.universeLift A`, with carrier in `Type (max uV uF)`, and finite length
of the derivative is carried back from the lift to `A`.

Namespace `Langlands.Derivative`. Every representation here is a complex
`SmoothRep.{0, uG, uV} ℂ G`, with coefficient universe `0`, group universe `uG`
and carrier universe `uV`.

## The transport predicate

- `TransportsEquiv J J'` is a Prop-valued definition. Here
  `J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H` and
  `J' : SmoothRep.{0,uG,uW} ℂ G ⥤ SmoothRep.{0,uH,uW} ℂ H` are two functors with
  the same groups but carriers in the universes `uV` and `uW`. The predicate says:
  for all `A` at `uV` and `B` at `uW`, if there is an equivalence
  `A.representation.Equiv B.representation`, then there is an equivalence
  `(J.obj A).representation.Equiv (J'.obj B).representation`.
  `Representation.Equiv` is Mathlib's equivalence of representations: a linear
  equivalence of the carriers that commutes with the group actions. The predicate
  asserts only that such an equivalence exists (`Nonempty`). It does not ask for
  a natural isomorphism.
- `transportsEquiv_id` says that the two identity functors satisfy the predicate.
  `transportsEquiv_comp` says that the predicate is preserved by composing
  functors.
- `equivOfLinearEquiv e he` builds an equivalence of representations from a linear
  equivalence `e` and a proof `he` that `e` commutes with the two actions. It
  is Mathlib's `Representation.Equiv.mk` with the commutation condition checked
  on each vector.

## Finite length along equivalences

- `hasFiniteLength_of_equiv e hA` says: if `e : A.representation.Equiv
  B.representation` and `A` has finite length, then `B` has finite length. The
  carriers of `A` and `B` may lie in different universes. The proof
  turns `e` into a surjective linear map of group-algebra modules
  `A.representation.asModule → B.representation.asModule`, using Mathlib's
  `Representation.IntertwiningMap.equivLinearMapAsModule`. It then applies
  Mathlib's `IsFiniteLength.of_surjective`, which allows the two modules to be in
  different universes.
- `hasFiniteLength_iff_of_equiv e` is the two-sided form, proved with `e.symm`.

## The functors in the telescope

Each lemma below has the form `TransportsEquiv (X.{…, uV} …) (X.{…, uW} …)` for one
published functor `X`, with every other argument the same. Like the
statement, all lemmas over the field `F` install `letI := T.topology` and take
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`.

The three basic functors:

- `continuousPullbackFunctor_transportsEquiv φ hφ`, for restriction
  `Mirabolic.continuousPullbackFunctor φ hφ` along a continuous homomorphism
  `φ : H →* G`. Restriction keeps the carriers, so the same linear equivalence
  works: it commutes with `h` acting through `φ h`.
- `twistFunctor_transportsEquiv χ hχ`, for `SmoothRep.twistFunctor χ hχ`, the
  twist by a character `χ : G →* ℂˣ` with open kernel. The same linear equivalence
  works, because it is linear and so commutes with multiplication by the scalar
  `χ g`.
- `localizationSmoothFunctor_transportsEquiv U θ M hMU hθ`, for
  `Jacquet.Localization.smoothFunctor U θ M hMU hθ`. This functor takes the
  `(U, θ)`-coinvariant quotient, with the descended action of a subgroup `M` that
  normalizes `U`. The linear equivalence of quotients is the published
  `Jacquet.Localization.representationEquiv U θ e` of
  `Langlands.Representation.Jacquet.LocalizationTransport`. Every element of
  the quotient is `Jacquet.Localization.mk … v` for some `v`
  (`Jacquet.Localization.mk_surjective`). So it suffices to check commutation with
  `m ∈ M` on such elements. There it is the commutation of `e` with `m`.

The minus functors and the derivatives are compositions of these three. In each
case below the composition holds by definition, and the lemma is
`transportsEquiv_comp` applied to the lemmas for the pieces:

- `psiMinusUnnormalized_transportsEquiv` and `phiMinusUnnormalized_transportsEquiv`,
  for `Mirabolic.psiMinusUnnormalized T n` and `Mirabolic.phiMinusUnnormalized T ψ n`.
  Each is localization followed by restriction.
- `psiMinus_transportsEquiv` and `phiMinus_transportsEquiv`, for the normalized
  `Mirabolic.psiMinus T n` and `Mirabolic.phiMinus T ψ n`. Each is the
  unnormalized functor followed by the determinant twist.
- `phiMinusIterate_transportsEquiv T ψ n k`, for `phiMinusIterate T ψ n k`, by
  induction on `k`. At `k = 0` it is the identity functor. At `k + 1` it is
  `Mirabolic.phiMinus T ψ (n + k) ⋙ phiMinusIterate T ψ n k`.
- `mirabolicDerivative_transportsEquiv`, for
  `mirabolicDerivative T ψ n k = phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n`.
- `generalLinearRestriction_transportsEquiv`, for `generalLinearRestriction T n`.
  This is restriction to the mirabolic subgroup.
- `generalLinearDerivativePositive_transportsEquiv`, for
  `generalLinearDerivativePositive T ψ n k = generalLinearRestriction T (n + k) ⋙
  mirabolicDerivative T ψ n k`.
- `generalLinearRankCast_transportsEquiv T h`, for the rank cast
  `generalLinearRankCast T h` along `h : a = b`. After `subst h` this is the
  identity functor.
- `generalLinearDerivative_transportsEquiv T ψ N k hk`, for
  `generalLinearDerivative T ψ N k hk`, by cases on `k`. At `k = 0` it is the
  identity functor. At `k + 1` it is
  `generalLinearRankCast T _ ⋙ generalLinearDerivativePositive T ψ (N - (k + 1)) k`.
  This is the published definition, which the published lemmas
  `generalLinearDerivative_zero` and `generalLinearDerivative_succ` record.

## The consequence used downstream

`generalLinearDerivative_hasFiniteLength_iff_of_equiv T ψ N k hk A B e` takes
`A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)`,
`B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier)` and an equivalence
`e : A.representation.Equiv B.representation`. It states

```
((generalLinearDerivative.{uF, uV} T ψ N k hk).obj A).HasFiniteLength ↔
  ((generalLinearDerivative.{uF, uW} T ψ N k hk).obj B).HasFiniteLength
```

It combines `generalLinearDerivative_transportsEquiv` with
`hasFiniteLength_iff_of_equiv`. The universes `uF`, `uV` and `uW` are
independent.

## Provenance

This module is internal infrastructure. The Library's carrier universes are
explicit, so a representation and its universe lift are distinct objects, and
the derivative at one carrier universe is a different functor from the
derivative at another. This module bridges the two. It has no counterpart in
Bernstein–Zelevinsky (1977) or in any other source, where an isomorphism
invariance of this kind is tacit. It proves no
statement of the source. The functors it treats are the published ones of
`Iteration`, `MirabolicMinus`, `Category/Twist` and `Jacquet/Localization`,
used unchanged.

## Imports and independence

Direct imports: `Langlands.Representation.Derivative.Iteration`, for the
derivative functors, and `Langlands.Representation.Jacquet.LocalizationTransport`,
for `Jacquet.Localization.representationEquiv`. The `Langlands` import closure
of this module, not counting the module itself, has 53 modules. It is the
52-module closure of `Iteration` (`Iteration` included) together with
`Jacquet.LocalizationTransport`. That is, it consists of `Iteration`,
`MirabolicMinus`, `MirabolicCharacter`, and modules on groups (`Group.GL`), local
fields, topology, smooth representations and their transfer, admissibility
cofinality, twists, coinvariants and localization, matrix coefficients and
Whittaker characters. It contains no classification, segment, multisegment,
square-integrable, tempered, socle, cuspidal-support, Jacquet-formula,
exactness or Leibniz-filtration module. The module uses no result of
Zelevinsky (1980) and nothing from the special-head criterion task
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95` or the other excluded tasks listed in
`GeneralLinearDerivativeFiniteLengthProof`.
