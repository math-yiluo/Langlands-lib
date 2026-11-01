# Normalization along a Zariski chart

This internal proof development transports finite normalization from a
subalgebra to an open chart and patches chartwise finiteness. It supports
the characteristic-zero part of integer finite-type normalization. The
lemmas are derived from the universal property of localization, Mathlib's
compatibility of integral closure with localization, and finite generation
on a basic-open cover; they make no additional literature claim.

`isFractionRing_of_surjective_awayMap` treats a subalgebra `C` of a domain
`A` and a nonzero element `r` of `C`. Surjectivity of the map `C[1/r]` to
`A[1/r]` says that a power of `r` times each element of `A` lies in `C`.
Write the numerator and denominator of an element of `FractionRing A` in
this form. Their ratio is a ratio of elements of `C`. The natural map
from `C` to the field is injective, so this proves that the same field is
a fraction field for `C`.

`finite_integralClosure_of_localization` allows compatible coefficient
rings `R → S → K`, where `S` localizes `R` away from `r` and the image of
`r` is already invertible in `K`. It constructs the natural inclusion
from the integral closure of `R` in `K` to that of `S` in `K`, using
upward transitivity of integrality. Mathlib's
`IsLocalization.Away.integralClosure` identifies the second closure as
the localization of the first. `Module.Finite.of_isLocalization` therefore
transports finite generation over `R` to finite generation over `S`.
Here `K` may be any commutative ring satisfying the displayed localization
hypothesis; a field is not required.

`finite_localizedModule_integralClosure` makes the corresponding module
identification when `S` is the canonical localization `Localization.Away r`.
The closure of `S` in `K` and `LocalizedModule.Away r (integralClosure R K)`
both localize the same `R`-module. The uniqueness equivalence supplied by
`IsLocalizedModule.linearEquiv` extends to an equivalence linear over `S`.
Finite generation of the closure over `S` transports across this equivalence.

`finite_normalization_localized_of_finite_subalgebra` applies these lemmas
to a subalgebra `C ⊆ A` of a domain and a nonzero `r : C` for which the
canonical map `C[1/r] → A[1/r]` is bijective. Its assumption is that the
normalization of `C` in its own canonical fraction field is finite over `C`.
The first lemma identifies `FractionRing A` as another fraction field for
`C`, and the induced equivalence of integral closures transports the
finiteness assumption. The chart bijection installs `A[1/r]` as a
localization of `C` as well as of `A`. Localizing the closure over `C`
and then identifying the result with the localized normalization module
over `A` gives

```text
Module.Finite (Localization.Away r.val)
  (LocalizedModule.Away r.val (integralClosure A (FractionRing A))).
```

`finite_of_finite_localizations_near_maximal` applies to any module `M`
over a commutative ring `R`. Suppose every maximal ideal omits some `r`
for which `M[1/r]` is finite over `R[1/r]`. The set of all such `r`
generates the unit ideal: otherwise a maximal ideal containing its span
contradicts the assumption. `Module.Finite.of_localizationSpan` then
proves `Module.Finite R M`. This argument also covers the zero ring.

All universes remain arbitrary. The only domain hypothesis occurs in the
two chart lemmas that use fraction fields.
