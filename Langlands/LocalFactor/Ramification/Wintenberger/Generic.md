# The generic ramification filtrations of the FontaineWintenberger library and of the Library

Module `Langlands.LocalFactor.Ramification.Wintenberger.Generic`, namespace
`Langlands.Ramification.Wintenberger`.

Both libraries define the lower ramification groups of a group acting on a ring as inertia
subgroups of powers of the maximal ideal (Mathlib's `Ideal.inertia`), with the whole group at
indices `≤ −1`, real indices read at the ceiling, and the upper groups as the lower groups at the
inverse Herbrand function. They differ in the Herbrand function: the FontaineWintenberger library
defines it as an integral of lower-group orders, the Library as a polygon by a finite sum of
clamped linear functions. This file proves that the two constructions give the same functions and
the same groups.

## Main statements

For a group `G` acting on a local ring `R` by ring automorphisms:

- `lowerRamificationGroup_maximalIdeal_eq_lowerGroupInt (n : ℤ) :
  FontaineWintenberger.lowerRamificationGroup G (IsLocalRing.maximalIdeal R) n =
  Langlands.Ramification.lowerGroupInt R G n`. For `n < 0` both are `⊤`; for `n ≥ 0` both are
  the inertia subgroup of the `(n + 1)`-st power of the maximal ideal.

For a local-field realization `T : LocalField.TopologicalData K₀ L` of an extension `L` of `K₀`,
an intermediate field `K` (`[Algebra K₀ K] [Algebra K L] [IsScalarTower K₀ K L]`), the action
`Local.integerAction T K` of `L ≃ₐ[K] L` on `T.Integers`, and, from the third item on,
`[FiniteDimensional K₀ L]`:

- `integers_isDiscreteValuationRing : IsDiscreteValuationRing T.Integers`.
- `lowerRamificationGroup_eq_lowerRamificationGroupInt (n : ℤ) :
  FontaineWintenberger.lowerRamificationGroup (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal T.Integers) n
  = Local.lowerRamificationGroupInt T K n`, and
  `card_lowerRamificationGroup_eq_lowerGroupOrder (m : ℕ)`: the orders at natural indices are
  `Local.lowerGroupOrder T K m`.
- `automorphismGroup_finite : Finite (L ≃ₐ[K] L)`.
- `herbrandFunction_eq_herbrandPhi (t : ℝ) :
  FontaineWintenberger.herbrandFunction (R := T.Integers) (L ≃ₐ[K] L) t = Local.herbrandPhi T K t`,
  for every real `t`.
- `inverseHerbrandFunction_eq_herbrandPsi {v : ℝ} (hv : -1 ≤ v) :
  FontaineWintenberger.inverseHerbrandFunction (R := T.Integers) (L ≃ₐ[K] L) v =
  Local.herbrandPsi T K v`. Below `−1` the FontaineWintenberger inverse is clamped at `−1` and the
  Library's is the identity, so the two differ there.
- `upperRamificationGroup_eq_upperRamificationGroup (v : ℝ) :
  FontaineWintenberger.upperRamificationGroup (R := T.Integers) (L ≃ₐ[K] L) v =
  Local.upperRamificationGroup T K v`, for every real `v`.

In these statements the action, the discrete valuation ring structure and the finiteness are
installed by `letI` from `Local.integerAction T K`, `integers_isDiscreteValuationRing T` and
`automorphismGroup_finite K`.

## Proofs

The Herbrand functions are both the identity on `(−∞, 0]`. On each interval `[n, n + 1]` with
`n` natural, the FontaineWintenberger function is affine with slope `|G_{n+1}| / |G_0|`
(`FontaineWintenberger.herbrandFunction_affine`), and so is the Library's polygon
(`Herbrand.polygon_on_unit_interval`, using that the orders are one past the cutoff,
`Local.lowerGroupOrder_tail`). Induction on `n` gives equality at the integers and then on every
interval. The inverses agree on `[−1, ∞)` because the Library's `Local.herbrandPhi` is strictly
increasing. For the upper groups at `v < −1`, the FontaineWintenberger inverse is `−1` and the
Library's is below `−1`; both lower groups are then the whole group.

## Declarations used

From the FontaineWintenberger library: `lowerRamificationGroup`, `lowerRamificationGroupReal`,
`herbrandFunction`, `herbrandFunction_affine`, `herbrandFunction_of_nonpos`,
`inverseHerbrandFunction`, `herbrandFunction_inverseHerbrandFunction`,
`inverseHerbrandFunction_of_nonpos`, `upperRamificationGroup`. From the Library:
`lowerGroupInt`, `lowerGroupInt_nat`, `Local.integerAction`, `Local.lowerRamificationGroupInt`,
`Local.lowerGroupOrder`, `Local.lowerGroupOrder_tail`, `Local.ramificationCutoff`,
`Local.herbrandPhi`, `Local.herbrandPhi_strictMono`, `Local.herbrandPsi`,
`Local.upperRamificationGroup`, `Herbrand.polygon_on_unit_interval`.

## Sources

Serre, *Local Fields*, Chapter IV, §1 (lower ramification groups) and §3 (the function `φ` as the
integral of `(G_0 : G_t)^{-1}`, its piecewise linear description, its inverse `ψ`, and the upper
numbering `G^v = G_{ψ(v)}`). Wintenberger 1983, §1.1, recalls the same conventions.
