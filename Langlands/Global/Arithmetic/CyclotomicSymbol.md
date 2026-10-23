# Explicit cyclotomic symbols over ℚ

This module defines the explicit local symbols of the cyclotomic extension `ℚ(ζ_m) / ℚ`,
with values in `(ℤ/m)ˣ ≅ Gal(ℚ(ζ_m)/ℚ)`. It proves their product formula on `ℚˣ`. These
are Artin–Tate's symbols `σ_p` (Chapter VII §2) and the local maps `φ_v` of Milne's
Example VII.8.2. They are the explicit side of the reciprocity law for cyclic cyclotomic
extensions in task fb66219f. The module makes no reference to class field theory. Galois
groups enter only in later modules, through `ζ ↦ ζ^c` for `c ∈ (ℤ/m)ˣ`.

All declarations are in the namespace `Langlands.Global.CyclotomicSymbol`. Throughout, `m` is
a nonzero natural number (`[NeZero m]`) and `p` a prime (`[Fact p.Prime]`). Write
`m = p^r · m₀` with `p ∤ m₀`. In Lean, `r = m.factorization p`, the `p`-part is
`p ^ m.factorization p`, and the prime-to-`p` part is `m / p ^ m.factorization p`.

## Definitions

- `unitPart p a : ℤ_[p]ˣ` is the unit `a · p^{-v(a)}` for `a ∈ ℚ_[p]ˣ`, where
  `v = Padic.valuation`. The norm computation is `norm_mul_zpow_neg_valuation`.
  `unitPartHom p : ℚ_[p]ˣ →* ℤ_[p]ˣ` and `valuationHom p : ℚ_[p]ˣ →* Multiplicative ℤ` are
  the unit part and the valuation as homomorphisms.
- `reduction m q : (ZMod m)ˣ →* (ZMod (q ^ m.factorization q))ˣ` reduces modulo the
  `q`-part of `m`.
- `crtUnits m p` is the Chinese remainder isomorphism
  `(ℤ/p^r)ˣ × (ℤ/m₀)ˣ ≃* (ℤ/m)ˣ`. It is Mathlib's `ZMod.chineseRemainder` on units,
  transported along `p^r · m₀ = m`.
- `primeUnit m p : (ZMod m₀)ˣ` is the class of `p`, a unit since `p ∤ m₀`.
- `localSymbol m p : ℚ_[p]ˣ →* (ZMod m)ˣ` is the local symbol. Write `a = p^μ u` with
  `μ = v(a)` and `u = unitPart p a`. The symbol of `a` corresponds under `crtUnits` to
  `(u⁻¹ mod p^r, p^μ mod m₀)`.
- `signUnit m : ℚˣ →* (ZMod m)ˣ` is the sign symbol at the real place: `α ↦ -1` if
  `α < 0` and `1` otherwise.
- `ratLocalSymbol m p : ℚˣ →* (ZMod m)ˣ` is `localSymbol m p` on rational units, via
  `ℚ → ℚ_[p]`. `primeSymbol m p` is the same for `p : Nat.Primes`.
- `symbolProduct m : ℚˣ →* (ZMod m)ˣ` is `α ↦ ∏ᶠ p : Nat.Primes, primeSymbol m p α`. The
  product has finite support (`mulSupport_primeSymbol_finite`), so it is a homomorphism.
- `primeRatUnit ℓ hℓ : ℚˣ` is the rational unit given by a prime `ℓ`.

## Theorems

- `eq_one_of_reduction`: if a unit `x ∈ (ZMod m)ˣ` reduces to `1` modulo the `q`-part of
  `m` for every prime `q`, then `x = 1`. If `z = x - 1 ≠ 0`, then every `q^{v_q(m)}` divides
  `z.val`, so `m ∣ z.val < m`, a contradiction. `eq_of_reduction` is the two-unit form.
- `reduction_localSymbol_self`: modulo the `p`-part of `m`, `localSymbol m p a` is the
  inverse of `unitPart p a` reduced by `PadicInt.toZModPow`.
- `reduction_localSymbol_of_ne`: modulo the `q`-part of `m` for a prime `q ≠ p`,
  `localSymbol m p a` is `p ^ v(a)`.
- `localSymbol_of_not_dvd`: if `p ∤ m`, then `localSymbol m p a = p ^ v(a)` in `(ZMod m)ˣ`.
  The symbol is unramified, and the class of `p` acts on `ζ_m` as the arithmetic Frobenius
  `ζ ↦ ζ^p`.
- `localSymbol_eq_one`: if `‖a - 1‖ ≤ p^{-r}` and `‖a - 1‖ < 1`, then `localSymbol m p a = 1`.
  Such an `a` is a unit with `a ≡ 1 mod p^r`. This is the local constancy of the symbol.
- Rational values: `reduction_ratLocalSymbol_self`, `reduction_ratLocalSymbol_of_ne`,
  `coe_unitPart_ratCast`, `valuation_ratCast_unit` (the `p`-adic valuation of a rational
  number is `padicValRat`), `padicValRat_neg_one`, `padicValRat_primeRatUnit`, and
  `ratLocalSymbol_eq_one` (trivial when `p ∤ m` and `v_p(α) = 0`).
- `ratUnits_hom_ext`: two homomorphisms from `ℚˣ` to a commutative group agree if they agree
  on `-1` and on every prime. Write `α = ± |num| / den` and factor the natural numbers into
  primes (`induction_on_primes`).
- `product_formula`: for every `α ∈ ℚˣ`,
  `signUnit m α * symbolProduct m α = 1` in `(ZMod m)ˣ`,
  i.e. `sign(α) · ∏_p σ_p(α) = 1`. The proof reduces modulo the `q`-part of `m` for each
  prime `q` (`eq_one_of_reduction`). The reduced product is a homomorphism in `α`, so it
  suffices to check generators (`ratUnits_hom_ext`).
  - `α = -1`: the sign and the factor at `q` are both `-1`, since `u = -1`. All other
    factors are `1`.
  - `α = ℓ ≠ q`: the factor at `q` is `ℓ⁻¹`, from `u = ℓ`, and the factor at `ℓ` is `ℓ`.
  - `α = q`: every factor is `1`, since `u = 1` at `q`.

## Sources and provenance

- Milne, *Class Field Theory* v4.03 (`milne-2020-class-field-theory`), Example VII.8.2,
  printed pp.221–222 (PDF pp.230–231). For `m = l^r`, `[n]` is `ζ ↦ ζ^n`. The local maps
  are `φ_∞(a) = [sign(a)]`, `φ_p(u p^s) = [p^s]` for `p ≠ l`, and `φ_l(u l^s) = [u⁻¹]`.
  Milne checks `∏_v φ_v(a) = 1` on `a = -1`, `a = l` and primes `q ≠ l`.
- Artin–Tate (`artin-tate-2009-class-field-theory`), Chapter VII §2, in particular
  Theorem 5 on printed p.41 (PDF p.50), which identifies `σ_p` with the local norm residue
  symbol.

Provenance is derived. The definition for a general modulus `m` combines Milne's
prime-power formulas through the Chinese remainder theorem. For `m = l^r` it is exactly
Milne's. The product formula is proved by reduction modulo prime powers and a check on
generators, as in Milne's example. Indexing the primes by `Nat.Primes` and taking the
product with `finprod` are formalization choices.
