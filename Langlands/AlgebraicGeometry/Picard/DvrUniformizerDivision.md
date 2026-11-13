# Dividing functions by the uniformizer on an abelian scheme over a DVR

Author: Worker 171.

Module `Langlands.AlgebraicGeometry.Picard.DvrUniformizerDivision`, namespace
`Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry`. Here `R` is a discrete
valuation domain, `A` an abelian scheme over `Spec R`, `π` irreducible and
`unifRes A π W` the restriction of `unifX A π` to an open `W` of the total space.

- `basicOpen_unifRes`, `res_unifRes`: the principal open of `unifRes A π W` is
  `W ⊓ D(unifX A π)`, and restricting `unifRes` gives `unifRes`.
- `eq_zero_of_unifRes_mul_eq_zero`: `unifRes A π W` is a nonzerodivisor on
  `Γ(A.X.left, W)`. The total space is integral; for nonempty `W` the section ring is
  a domain and `unifRes` is nonzero because `W` meets the nonempty principal open of
  `unifX`.
- `exists_eq_unifRes_mul_of_isAffineOpen`: on an affine open `V`, a function whose
  principal open misses the special fibre is `unifRes A π V` times a function. The
  map `R → Γ(A.X.left, V)` is smooth (`HasRingHomProperty.appLE`), points of `V`
  correspond to primes (`IsAffineOpen.fromSpec_preimage_basicOpen`), and
  `SmoothDVRUniformizerDivision.dvd_of_forall_mem_prime` applies.
- `exists_eq_unifRes_mul`: the same for an arbitrary open `U`. Divide on an affine
  cover inside `U`; the quotients agree on overlaps because `unifRes` is a
  nonzerodivisor; glue them with the sheaf condition of the structure sheaf
  (`TopCat.Sheaf.existsUnique_gluing'`, `eq_of_locally_eq'`).
- `eq_zero_of_forall_unifRes_pow_dvd`: a function on `W` divisible by every power of
  `unifRes A π W` vanishes if `W` contains a point of the special fibre. Its germ
  there lies in every power of a proper principal ideal of the noetherian local stalk
  (Krull, `Ideal.iInf_pow_eq_bot_of_isLocalRing`), and germs are injective on an
  integral scheme.

Internal infrastructure derived from published Library and Mathlib results; no
external source is asserted.
