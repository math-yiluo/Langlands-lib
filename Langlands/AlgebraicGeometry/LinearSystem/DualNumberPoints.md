# Points of `Spec K` and `Spec K[ε]` in an open

This helper module is used in the proof of
`Langlands.AlgebraicGeometry.LinearSystemMorphismStatement` and in the proof of
`Langlands.AlgebraicGeometry.FiniteSeparatingSectionsStatement`. It is internal: it is not a
Library statement and has no literature source of its own. It uses that any two points of
the spectrum of a field `K`, or of its dual numbers `K[ε] = K[X]/(X²)` (Mathlib's
`DualNumber K`), are equal. For `Spec K` this comes from Mathlib's `Unique` instance for the
spectrum of a field; for `Spec K[ε]` it reuses the published
`Picard.subsingleton_primeSpectrum_dualNumber`. Everything is in the namespace
`Langlands.AlgebraicGeometry.LinearSystem`.

- `dualNumber_prime_eq_maximalIdeal`: every prime ideal `P` of `K[ε]` is the maximal ideal.
  `P` lies in the maximal ideal, which is `(ε)` by Mathlib's
  `DualNumber.maximalIdeal_eq_span_singleton_eps`. Conversely `ε² = 0 ∈ P`, so `ε ∈ P`.
- `subsingleton_spec_dualNumber`: `Spec K[ε]` has at most one point, by the
  published `Picard.subsingleton_primeSpectrum_dualNumber`.
- `forall_mem_of_mem`: if a rational point `x : Spec K ⟶ X` maps the closed point into an open
  `U`, then it maps every point of `Spec K` into `U`. `Spec K` has one point, so this is a
  rewrite.
- `forall_mem_of_augmentation_comp`: let `t : Spec K[ε] ⟶ X` satisfy
  `dualNumberAugmentation K ≫ t = x`, where Library's `dualNumberAugmentation K` is the
  closed point `Spec K ⟶ Spec K[ε]` (from `ε ↦ 0`). If `x` maps the closed point into `U`,
  then `t` maps every point of `Spec K[ε]` into `U`. Every point of `Spec K[ε]` is the image
  of the closed point of `Spec K`, by `subsingleton_spec_dualNumber`.
