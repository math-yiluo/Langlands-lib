# Roots of units in a strictly Henselian local ring and units of `R[1/t]`

The module `Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits`
collects the elementary ring-theoretic facts used in Kummer theory. For a
positive integer `m` invertible in a strictly Henselian local ring `R`,
units have `m`-th roots and primitive `m`-th roots of unity exist. In a local
ring with `m` invertible, `m`-th roots of unity remain distinct after any map
to a nonzero ring. For a prime element `t` in a domain `R`, units of
`R[1/t]` have the form `u · t^k`. All declarations live in the namespace
`Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits`; the rings live in
arbitrary universes.

## Hensel lifting

For a Henselian local ring `R` (Mathlib's `HenselianLocalRing`):

- `exists_pow_eq_lift`: if `m ≠ 0` is invertible in `R`, `u` is a unit and
  `a₀` satisfies `res(a₀)^m = res(u)` in the residue field, then there is `w`
  with `w^m = u` and `res(w) = res(a₀)`.

Proof: `a₀` is a unit (otherwise `res(u) = 0`), so the derivative `m·a₀^(m-1)`
of the monic polynomial `X^m - u` at `a₀` is a unit while its value lies in
the maximal ideal. Mathlib's defining property `HenselianLocalRing.is_henselian`
gives a root `w` congruent to `a₀`.

## Strictly Henselian rings

Assume further that the residue field is separably closed
(`IsSepClosed (ResidueField R)`), that is, `R` is strictly Henselian.

- `exists_pow_eq_of_isUnit`: every unit of `R` is an `m`-th power for `m ≠ 0`
  invertible in `R`. The polynomial `X^m - res(u)` is separable over the
  residue field (Mathlib's `separable_X_pow_sub_C`), so it has a root there
  (`IsSepClosed.exists_root`), which `exists_pow_eq_lift` lifts.
- `exists_isPrimitiveRoot`: for `m ≠ 0` invertible in `R`, `R` contains a
  primitive `m`-th root of unity. A
  primitive root of unity of the residue field
  (`HasEnoughRootsOfUnity.exists_isPrimitiveRoot`) lifts by
  `exists_pow_eq_lift` with `u = 1` to a root `ζ` of `X^m - 1`; a smaller
  power `ζ^l = 1`, `0 < l < m`, would reduce to the same relation in the
  residue field, which is excluded there.

## Roots of unity in a local ring

For a local ring `R` and `m` invertible in `R`:

- `eq_one_of_pow_eq_one_of_sub_mem`: if `ζ^m = 1` and `ζ ≡ 1` modulo the
  maximal ideal, then `ζ = 1`. The geometric sum `1 + ζ + ⋯ + ζ^(m-1)`
  reduces to `m`, a unit, and its product with `ζ - 1` is `ζ^m - 1 = 0`.
- `eq_one_of_pow_eq_one_of_map_eq_one`: if `ζ^m = 1` and `φ(ζ) = 1` for some
  ring homomorphism `φ` to a nonzero ring, then `ζ = 1`: the element `ζ - 1`
  maps to `0`, so it is not a unit, so it lies in the maximal ideal.

## Units of `R[1/t]`

- `exists_eq_unit_mul_zpow`: for a domain `R`, a prime element `t` and a unit
  `a` of `Localization.Away t`, there are a unit `u` of `R` and an integer `k`
  with `a = u · t^k` in `R[1/t]`.

Proof: write `a = r/t^i` and `a⁻¹ = r'/t^j` with `r, r' ∈ R`. Injectivity of
`R → R[1/t]` (a domain, `t ≠ 0`) gives `r r' = t^(i+j)` in `R`, so `r`
divides a power of the prime `t`; Mathlib's `dvd_prime_pow` gives
`r = u · t^e` with `u` a unit, and then `a = u · t^(e - i)`.

## Provenance

These are standard facts of commutative algebra (Hensel's lemma for simple
roots; the structure of units of a localization of a domain at a prime
element). They are the inputs used in the Kummer-theoretic proof of the
Library proposition `StrictlyHenselianKummerFactorizationStatement`, where
`R` is a strictly Henselian regular local domain and `t` a regular parameter.
