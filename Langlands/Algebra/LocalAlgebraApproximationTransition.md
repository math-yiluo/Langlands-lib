# Prime localization for the concrete approximation transitions

This internal part of the Stacks 00QV construction uses the presentation and
stages from `LocalAlgebraApproximationExistence`. The relation ideal at a later
stage is the extension of the earlier ideal: each original relation has all its
coefficients in every base ring, and coefficient inclusion is injective.

The polynomial pushout therefore descends to the actual quotient maps. The
localized stages and their transition agree with those quotient maps. Applying
the tensor localization criterion then gives prime localization for the actual
`LocalAlgebraSystem.ringBaseChangeMap`, with its induced algebra structure.
This is the prime localization clause of the construction, not a separate
assumption on the published existence statement.

## Declarations

- `Langlands.Algebra.isPushout_quotient_of_ideal_map_eq` restates the quotient pushout
  criterion `isPushout_quotient_of_compatible_map` for a later ideal `J` that is only
  propositionally equal to the extension `I.map (algebraMap Q Q')`.
- `Pres.rel_map`: `(P.rel i).map (P.polyMap h) = P.rel j`. The inclusion `≤` is
  `rel_le_comap`. For `≥`, a generator `g` of `P.rel j` has `toPoly j g ∈ F`. Its
  coefficients lie in `P.B i` (`mem_B_of_mem_F`), so it lifts to some `g'` over `P.B i` with
  `polyMap h g' = g` (injectivity of `toPoly j`).
- `Pres.AMap_C`: `AMap` is compatible with the base structure maps.
- `Pres.isPrimeLocalization_system`: the polynomial rings form a pushout through Mathlib's
  `MvPolynomial.algebraMvPolynomial` instance, and the quotients then form a pushout by
  `rel_map`. The localizations `P.Sl i` and `P.Sl j` are at `(P.q i).primeCompl` and
  `(P.q j).primeCompl`, and `SlMap_algebraMap` gives the transition compatibility.
  `LocalAlgebraSystem.isPrimeLocalization_of_quotient_pushout` then yields
  `P.system.IsPrimeLocalization h`.
