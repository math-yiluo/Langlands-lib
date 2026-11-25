# Finite upper ramification groups: the spectral integers of the two libraries

Module `Langlands.LocalFactor.Ramification.Wintenberger.Finite`, namespace
`Langlands.Ramification.Wintenberger`.

Let `K₀` be a nontrivially normed field, ultrametric, complete and locally compact, with a
valuative relation induced by its norm (`hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b`),
and `E` a finite extension of `K₀`. The Library computes ramification groups on the integer ring
of its canonical realization `LocalField.canonicalTopologicalData K₀ E hbase`, whose valuation is
the spectral norm over `K₀`. The FontaineWintenberger library computes the ramification groups of
a finite Galois extension `E/K` over a normed base `K` on `spectralIntegerRing K E`, the unit ball
of the spectral norm over `K`. When `K` is a normed extension of `K₀`, the two rings have the same
elements and the two families of upper groups agree.

## Main statements

- `mem_canonicalIntegers_iff (x : E) : x ∈ (LocalField.canonicalTopologicalData K₀ E hbase).Integers
  ↔ spectralNorm K₀ E x ≤ 1`.
- `spectralNorm_eq_of_tower [Algebra.IsAlgebraic K₀ E] (x : E) :
  spectralNorm K E x = spectralNorm K₀ E x`, for a normed extension `K` of `K₀`
  (`[NormedAlgebra K₀ K] [IsUltrametricDist K] [CompleteSpace K]`) with
  `[Algebra K E] [IsScalarTower K₀ K E]`. On `E` with the spectral norm over `K₀`, Mathlib's
  `spectralNorm.normedAlgebra'` makes `E` a normed `K`-algebra, and `NormedAlgebra.norm_eq_spectralNorm`
  identifies that norm with the spectral norm over `K`.
- `spectralIntegerRing_eq_canonicalIntegers [Algebra.IsAlgebraic K E] :
  (FontaineWintenberger.spectralIntegerRing K E).toSubring =
  (LocalField.canonicalTopologicalData K₀ E hbase).Integers`, and the ring isomorphism
  `spectralIntegerRingEquiv`, the identity on elements.
- `upperRamificationGroup_eq_max (v : ℝ)`: the FontaineWintenberger upper groups of a finite group
  acting on a discrete valuation ring do not change when `v` is replaced by `max v (−1)`.
- `upperRamificationGroup_spectral_eq_canonical (v : ℝ) :
  FontaineWintenberger.upperRamificationGroup (R := FontaineWintenberger.spectralIntegerRing K E)
  (E ≃ₐ[K] E) v = Local.canonicalUpperRamificationGroup K₀ E hbase K v`, for
  `[NormedAlgebra K₀ K] [FontaineWintenberger.IsCompleteDiscreteValuedField K]`, `E` finite Galois
  over `K` and finite over `K₀`, and every real `v`.

## Proof of the last statement

By `Generic.upperRamificationGroup_eq_upperRamificationGroup`, the Library's group is the
FontaineWintenberger upper group for the action on the Library's integer ring. Both sides may be
evaluated at `max v (−1)`. There, the FontaineWintenberger transport lemma
`upperRamificationGroup_map_equivariant`, applied to `spectralIntegerRingEquiv` and the identity
of `E ≃ₐ[K] E` (both actions apply the automorphism to the underlying element), identifies the
groups on the two rings.

## Declarations used

From the FontaineWintenberger library: `spectralIntegerRing`, `mem_spectralIntegerRing`,
`spectralIntegerRingGaloisAction` (the action of `E ≃ₐ[K] E`), `upperRamificationGroup`,
`inverseHerbrandFunction`, `upperRamificationGroup_map_equivariant`, and the instance
`spectralIntegerRing_isDiscreteValuationRing`. From the Library:
`LocalField.canonicalTopologicalData`, `LocalField.canonicalValuativeRel`,
`LocalGalois.spectralValuation`, `Local.canonicalUpperRamificationGroup`, `Local.integerAction`.
From Mathlib: `spectralNorm.normedAlgebra'`, `NormedAlgebra.norm_eq_spectralNorm`.

## Sources

Serre, *Local Fields*, Chapter II, §2 (the extension of the absolute value of a complete field to
a finite extension is unique, and its valuation ring is the integral closure) and Chapter IV, §3
(upper numbering of a finite Galois extension).
