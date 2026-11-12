# Adele rings are not noetherian

Author: Worker 3519.

`AdeleRingNotNoetherianStatement` states a remark of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module contains one
Prop-valued statement and no proof.

## Source

Printed p.5, in the discussion before Theorem 3.4 of finitely presented schemes over a ring
`R`, for a global field `F`: "Finite presentation coincides with finite type when `R` is
noetherian, but the adele ring `A_F` is not noetherian." The remark explains why the paper
works with finitely presented, not merely finite type, `A_F`-schemes.

## Statement

`AdeleRingNotNoetherianStatement` is the conjunction of two assertions, for types in one
universe `u`:

1. for every number field `K`, the ring `Adeles K` is not noetherian
   (`¬ IsNoetherianRing (Adeles K)`). `Adeles K` is the Library's abbreviation for Mathlib's
   `NumberField.AdeleRing (𝓞 K) K`: the product of the infinite adele ring (all archimedean
   completions) and the finite adele ring (the restricted product of the completions at the
   nonzero primes of `𝓞 K` with respect to their valuation rings);
2. for every function field `F` over a field `k` (`FunctionField k F`, with
   `Algebra (RatFunc k) F` and the scalar tower `k → RatFunc k → F`), the ring
   `CurvePlaceAdeleRing k F` is not noetherian. `CurvePlaceAdeleRing k F` is the Library's
   restricted product of the completions of `F` at all actual discrete places trivial on `k`
   (`AlgebraicCurve.Place k F`) with respect to their valuation rings.

Conrad's global function fields have finite constant field. Part 2 allows an arbitrary
constant field `k`, so it contains the source's function-field case (`k` finite) as a special
case. The ring structure only is concerned; no topology enters.

## Why it holds

This explanation is provenance; the file proves nothing. In both cases the ring is (a factor
of) a restricted product over an infinite set of places with nonzero factors: there are
infinitely many nonzero primes of `𝓞 K`, and `AlgebraicCurve.Place k F` is infinite for every
constant field (Library theorem `functionField_places_infinite`). For a finite set `T` of
places, the elements supported in `T` (zero outside `T`) form an ideal `I_T`, and the
indicator idempotent of `T` lies in the restricted product. A strictly increasing sequence of
finite sets `T` gives a strictly increasing chain of ideals `I_T`, so the ring is not
noetherian.

## Provenance

The assertion is Conrad's. The derived choices are the concrete adele rings used throughout
the Library's formalization of the paper (`Adeles K` for number fields and
`CurvePlaceAdeleRing k F` for function fields) and the extension of the function-field case to
arbitrary constant fields.
