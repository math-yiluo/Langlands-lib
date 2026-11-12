# Uniqueness of the essential vector from mirabolic restriction injectivity

This internal unit reduces the uniqueness clause of Jacquet 2012, Theorem 1 (printed
page 517) to a single representation-theoretic input. That input is injectivity of
restriction to the mirabolic subgroup, for one representation `π` of `GL_(n+2)(F)`
and one Whittaker functional `ℓ`. It does not prove that injectivity, nor the
existence of an essential vector. Both appear as explicit hypotheses of the
conditional results below.

## The injectivity predicate

`IsMirabolicRestrictionInjective π ℓ` says that the map
`v ↦ (p ↦ ℓ(π(p) v))`, from the carrier `V` of `π` to complex functions on the
published subgroup `mirabolic (n + 1) F` of `GL_(n+2)(F)`, is injective. The field
needs only a topology here, and the carrier universe is arbitrary.

This is the conclusion of the proposition requested by task
60a13dd3-f4bb-482d-b6a2-5246fe9bf558 (`MirabolicRestrictionInjectivityStatement`,
not yet published), specialized to one representation of rank `n + 2` and one
functional. That task cites Jacquet and Shalika 1981, Section 1.1, printed page 505:
for an irreducible admissible generic representation, `W ↦ W|P` is a bijection of
the Whittaker model onto the Kirillov space. Here the predicate is only a
hypothesis; no instance of it is claimed.

## Results

- `eq_zero_of_mirabolic_eq_zero`: under `IsMirabolicRestrictionInjective π ℓ`, a
  vector `w` of the published model `coefficientModel π ℓ` with `w(p) = 0` for every
  mirabolic `p` is zero. Write `w` as the coefficient function of some `v ∈ V`
  (`modelMap_surjective`). Then `v` and `0` have the same mirabolic restriction, so
  `v = 0` and `w = 0`.
- `IsEssentialVector.eq_of_mirabolicRestrictionInjective`: let `π` be smooth and
  `h` a Jacquet normalization. Under the injectivity hypothesis, two vectors `w₁, w₂`
  satisfying the published `IsEssentialVector h π ℓ` are equal. By
  `IsEssentialVector.eq_on_mirabolic` from `Conductor/EssentialRestrictionUniqueness`
  they agree on the mirabolic subgroup, so the previous result applies to
  `w₁ - w₂`.
- `existsUnique_isEssentialVector_of_exists`: under the same hypotheses, if some
  essential vector exists, then exactly one exists. This is the form
  `∃! w, IsEssentialVector h π ℓ w` used in the published
  `EssentialVectorStatement`.
- `existsUnique_isEssentialVector_of_isGeneric`: the same conclusion for a
  representation with `IsGeneric ψ (n + 1) π`, whose admissibility includes
  smoothness.
