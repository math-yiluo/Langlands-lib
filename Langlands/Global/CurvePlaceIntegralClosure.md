# Finite integral closure of actual function-field valuation rings

This module proves that the integral closure of an actual function-field
valuation ring in any finite upper field extension is a finite module. It
constructs the actual integral-closure ring, proves it is Dedekind with the
original upper field as fraction field, and obtains the fundamental
ramification-inertia degree sum on all its primes above the original maximal
ideal. The original rational-function presentation can be inseparable.

These are derived arithmetic prerequisites for Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 4.2,
printed page 10. That passage uses global-field arithmetic in the completed
tensor decomposition and the integral-model reduction. This unit supplies
finite normalization and the degree identity on its actual prime ideals;
comparison with all actual upper curve places remains separate.

## Arbitrary localization of finite integral closure

`Langlands.Global.finite_integralClosure_of_arbitrary_localization` is a
general ring lemma. For commutative rings `R`, `A` and `L` with compatible
algebra structures, a submonoid `M : Submonoid R`, and
`[IsLocalization M A]`, it proves

```text
Module.Finite R (integralClosure R L)
  → Module.Finite A (integralClosure A L).
```

The module-finiteness premise is supplied as an instance.
The three rings can lie in independent arbitrary universes.
The lemma does not require that `L` be a field.

The canonical map sends an element integral over `R` to the same element
integral over `A`. Every mapped denominator is already a unit in `A`,
and hence in `L`; therefore localizing the ambient ring `L` at those
denominators leaves `L` itself. Mathlib's
`IsLocalization.integralClosure` identifies the target integral closure
as the corresponding localization of the source integral closure.
`Module.Finite.of_isLocalization` then gives the conclusion.
This generalizes the existing away-localization helper in
`Langlands.AlgebraicGeometry.NoetherianApproximation.NormalizationLocalization`
to an arbitrary submonoid.

## Exact chart inclusion and localization

The declarations in `Langlands.Global.CurvePlaceIntegralClosure` first work
with fields `k`, `K` and `L` in one arbitrary common universe, a finite
constant field `k`, `Algebra k K`, `Algebra K L`, a parameter `s : K`,
`[FiniteDimensional k⟮s⟯ K]`, and an actual curve place
`p : AlgebraicCurve.Place k K`.

For a proof that `s` is integral at `p`, `chartIntegersMap` is the original
inclusion

```text
CurveModel.chartRing k {s} →+* p.toValuationSubring.
```

Its image is integral at `p` because the normalized chart consists of
elements integral over the parameter algebra contained in that valuation
ring. The map uses the original field elements throughout.

With `[FiniteDimensional K L]`, `finite_of_chart` proves module finiteness
of `integralClosure p.toValuationSubring L` over the original valuation
ring. Let `R` be the actual normalized parameter chart. The existing
`FiniteConstantCurveChart` results make `R` a normal noetherian domain
of finite type over the finite constants and hence over the integers,
with fraction field `K`. The published
`finite_integralClosure_of_normal_integer_finiteType` supplies finiteness
of `integralClosure R L`, including inseparable extensions.

The actual center prime `P` of `p` in `R` satisfies

```text
HeightOneSpectrum.valuationSubringAtPrime K P = p.toValuationSubring.
```

The proof uses that equality to construct an explicit `R`-algebra
equivalence and transports `IsLocalization P.asIdeal.primeCompl` to
the original valuation ring with the original inclusion.
The arbitrary-localization lemma then gives the required finiteness.
No abstract ring with an assumed identification is substituted for the
original valuation ring.

## Actual integral closure without a supplied chart

`Langlands.Global.curvePlaceIntegralClosure L p` is the existing integral
closure `integralClosure p.toValuationSubring L`. Its scalar structure
uses the original embedding `K → L` restricted to the original
valuation ring, as constructed in `CurvePlaceCompletionExtension`.
This ring definition requires neither finite constants nor a
function-field presentation.

The scoped instance `fractionRing` only adds
`[FiniteDimensional K L]` and gives the original `L` as its fraction
field.

The scoped instance `moduleFinite` assumes finite constants and the
original function-field data

```text
Algebra (RatFunc k) K,
IsScalarTower k (RatFunc k) K,
FunctionField k K,
FiniteDimensional K L.
```

It proves finiteness of the actual integral closure as a module over
`p.toValuationSubring`. Internally it chooses the image of the original
rational-function parameter. This parameter or its inverse is integral
at `p`. The existing equality of their generated intermediate fields
gives finite dimensionality for the inverse case. Applying
`finite_of_chart` in the appropriate case removes any chart choice or
integrality premise from the caller.

No algebra structure of the constants on `L`, compatible constant-field
tower to `L`, separability, chosen separating parameter or assumed
normalization finiteness is required.

## Dedekind structure and the fundamental identity

The scoped instance `dedekind` proves that the actual integral closure
is a Dedekind domain under the function-field hypotheses above.
Its noetherianness follows from module finiteness over the original
discrete valuation ring. Integrality gives dimension at most one, and
the integral-closure property gives integral closedness in `L`.

`finrank_eq` states that the integral-closure module rank over
`p.toValuationSubring` equals `Module.finrank K L`. This is the existing
fraction-field rank comparison. This particular equality does not need
finite constants or a function-field presentation.

With the function-field hypotheses, `sum_ramification_inertia` proves

```text
∑ P : p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p),
  P.val.ramificationIdx p.toValuationSubring
    * P.val.inertiaDeg p.toValuationSubring
      = Module.finrank K L.
```

The finite enumeration of this full prime-over subtype is derived
internally. The proof applies Mathlib's
`Ideal.sum_ramification_inertia_eq_finrank` to the actual finite
Dedekind extension and uses `finrank_eq`. It does not assume the
degree-sum identity or replace finite-module hypotheses by finite
type.

## Provenance and remaining comparisons

Source ID: `conrad-2011-weil-grothendieck-adelic-points`.
The registered 21-page original has SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The cited locator is Example 4.2, printed page 10, the global-field
completed-tensor product and integral-model reduction.

This explicit normalization construction and its localization proof
are derived prerequisite arithmetic. The normalization theorem, finite
chart comparisons and the general ramification-inertia sum theorem
are reused by their Lean names. The unit does not attribute this
specific implementation route as a separate assertion in Conrad.

The index of the final sum is all actual prime ideals of the integral
closure lying over the original maximal ideal. Identifying these
with all upper curve places and comparing their ramification and
inertia data remain necessary. Tensor injectivity, the associated
Weil point homeomorphism, integral models and passage to adelic
limits also remain obligations of the whole-paper task.
