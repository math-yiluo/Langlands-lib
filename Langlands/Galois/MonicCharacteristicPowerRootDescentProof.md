# Proof of the descent of monic power roots in characteristic zero

Module `Langlands.Galois.MonicCharacteristicPowerRootDescentProof`, name space
`Langlands.GaloisRepresentation`. It proves the published
`MonicCharacteristicPowerRootDescentStatement` of
[`HarrisKottwitzPowerNormalizationStatement`](HarrisKottwitzPowerNormalizationStatement.md)
in all its universes. It does not concern the second proposition of that file,
`HarrisKottwitzPowerNormalizationStatement`.

## Main declarations

```lean
theorem normalize_gcd_pow_succ_derivative {M : Type uW} [Field M] [CharZero M] [DecidableEq M]
    {P : M[X]} (hP : P.Monic) (b : ℕ) :
    normalize (EuclideanDomain.gcd (P ^ (b + 1)) (derivative (P ^ (b + 1)))) =
      P ^ b * normalize (EuclideanDomain.gcd P (derivative P))

theorem exists_map_eq_of_map_eq_pow {L : Type uL} [Field L] [CharZero L] {M : Type uW} [Field M]
    (ι : L →+* M) {a : ℕ} (ha : 0 < a) :
    ∀ (n : ℕ) (P : M[X]) (Q : L[X]), P.natDegree < n → P.Monic → Q.map ι = P ^ a →
      ∃ R : L[X], R.map ι = P

theorem monicCharacteristicPowerRootDescent :
    MonicCharacteristicPowerRootDescentStatement.{uL, uW}
```

The statement, as published (not changed):

```lean
def MonicCharacteristicPowerRootDescentStatement : Prop :=
  ∀ (L : Type uL) [Field L] [CharZero L] (M : Type uW) [Field M]
    (ι : L →+* M) (a : ℕ) (P : Polynomial M) (Q : Polynomial L),
    0 < a → P.Monic → Q.map ι = P ^ a →
    ∃! R : Polynomial L, R.Monic ∧ R.map ι = P ∧ R ^ a = Q
```

In words:

* `normalize_gcd_pow_succ_derivative`: over a field of characteristic zero, for monic `P` and
  `b ≥ 0`, the monic greatest common divisor of `P ^ (b + 1)` and its derivative is `P ^ b` times
  the monic greatest common divisor of `P` and `P'`. Here the greatest common divisor is Mathlib's
  Euclidean `EuclideanDomain.gcd` and `normalize` divides a nonzero polynomial by its leading
  coefficient.
* `exists_map_eq_of_map_eq_pow`: for a map of fields `ι : L →+* M` with `L` of characteristic
  zero and `a > 0`, every monic `P ∈ M[X]` of degree less than `n` whose power `P ^ a` is the
  image of some `Q ∈ L[X]` is itself the image of some `R ∈ L[X]`. The bound `n` is the variable of
  the induction; any `n > deg P` may be used.
* `monicCharacteristicPowerRootDescent` has the statement as its type, with its universe
  parameters `uL, uW` in this order.

Lean reports that `monicCharacteristicPowerRootDescent` depends on `propext`,
`Classical.choice` and `Quot.sound` only.

## Proofs

**The greatest common divisor of a power and its derivative.** Write `g` for the Euclidean greatest
common divisor of `P ^ (b + 1)` and `(P ^ (b + 1))' = (b + 1) P ^ b P'` (`derivative_pow_succ`), and
`u` for that of `P` and `P'`. Both `normalize g` and `P ^ b * normalize u` are monic
(`monic_normalize`, `P ≠ 0`), so it suffices that each divides the other
(`eq_of_monic_of_associated`, `associated_of_dvd_dvd`).

* `P ^ b u` divides `P ^ (b + 1) = P ^ b P` and `(b + 1) P ^ b P'`, because `u` divides `P` and
  `P'`; so it divides `g` (`EuclideanDomain.dvd_gcd`).
* By Bézout (`EuclideanDomain.gcd_eq_gcd_ab`), `u = P A + P' B` for some `A, B`. Since
  `b + 1 ≠ 0` in `M` (characteristic zero),
  `P ^ b u = P ^ (b + 1) A + (P ^ (b + 1))' ((b + 1)⁻¹ B)`, and `g` divides both terms.

**Existence of a preimage.** By induction on `n`. Let `P` be monic of degree less than `n + 1`,
and `Q.map ι = P ^ (b + 1)`. The field `M` has characteristic zero, because `ι` is injective
(`RingHom.charZero_iff`). If `P` has degree `0` it is `1`, the image of `1`. Otherwise:

1. Let `U` be the monic greatest common divisor of `P` and `P'`, and write `P = U T`. The
   derivative `P'` is nonzero of degree less than that of `P` (`derivative_ne_zero`,
   `natDegree_derivative_lt`, characteristic zero), and `U` divides it, so
   `deg U ≤ deg P' < deg P` (`natDegree_le_of_dvd`).
2. Let `G ∈ L[X]` be the monic greatest common divisor of `Q` and `Q'`. Normalization, Euclidean
   greatest common divisors and derivatives commute with `map ι` (`map_normalize`, `gcd_map`,
   `derivative_map`), so `G.map ι` is the monic greatest common divisor of `P ^ (b + 1)` and its
   derivative, which is `P ^ b U` by the first theorem.
3. Euclidean division commutes with `map ι` (`Polynomial.map_div`). Hence
   `(Q / G).map ι = P ^ (b + 1) / (P ^ b U) = T`, and
   `(Q / (Q / G) ^ (b + 1)).map ι = P ^ (b + 1) / T ^ (b + 1) = U ^ (b + 1)`
   (`EuclideanDomain.eq_div_of_mul_eq_right`, with `P ^ (b + 1) = (P ^ b U) T = T ^ (b + 1) U ^ (b + 1)`).
4. `U` is monic of degree less than `n` and `U ^ (b + 1)` is the image of a polynomial over `L`,
   so by induction `U = V.map ι` for some `V ∈ L[X]`. Then `P = T U = ((Q / G) V).map ι`.

**The statement.** Apply the existence to `n = deg P + 1` and obtain `R` with `R.map ι = P`. The
map `Polynomial.map ι` is injective (`map_injective`, `ι` injective) and preserves leading
coefficients up to `ι`, so:

* `R` is monic because `R.map ι = P` is (`monic_map_iff`);
* `R ^ a = Q` because both have image `P ^ a` (`Polynomial.map_pow`);
* a monic `R'` with `R'.map ι = P` equals `R`, since both have image `P`.

Uniqueness does not use the monicity or the power condition of `R'`.

## Declarations used

- From the Library: `MonicCharacteristicPowerRootDescentStatement`
  (`HarrisKottwitzPowerNormalizationStatement`).
- From Mathlib: `EuclideanDomain.gcd`, `EuclideanDomain.gcd_dvd_left`,
  `EuclideanDomain.gcd_dvd_right`, `EuclideanDomain.dvd_gcd`, `EuclideanDomain.gcd_eq_gcd_ab`,
  `EuclideanDomain.gcd_eq_zero_iff`, `EuclideanDomain.eq_div_of_mul_eq_right`,
  `Polynomial.gcd_map`, `Polynomial.map_div`, `Polynomial.map_normalize`,
  `Polynomial.monic_normalize`, `Polynomial.derivative_map`, `Polynomial.derivative_pow_succ`,
  `Polynomial.derivative_ne_zero`, `Polynomial.natDegree_derivative_lt`,
  `Polynomial.natDegree_le_of_dvd`, `Polynomial.Monic.natDegree_eq_zero`,
  `Polynomial.eq_of_monic_of_associated`, `Polynomial.monic_map_iff`, `Polynomial.map_injective`,
  `normalize_dvd_iff`, `dvd_normalize_iff`, `associated_normalize`, `associated_of_dvd_dvd`,
  `RingHom.charZero_iff`.

## Sources

The statement isolates the rationality of the coefficients of a monic root needed in Clozel,
*Représentations galoisiennes associées aux représentations automorphes autoduales de GL(n)*
(Publ. Math. IHÉS 73, 1991), §5.2, equations (5.11)–(5.12), (5.31) and the power identity on
p. 142; see [`HarrisKottwitzPowerNormalizationStatement`](HarrisKottwitzPowerNormalizationStatement.md)
for the provenance of the statement. The proof here is the elementary argument above and follows
no particular source. It replaces the comparison of coefficients from the leading end, which also
needs division by `a`, with the identity for the greatest common divisor of `P ^ a` and its
derivative, which needs division by `a` in the same way.
