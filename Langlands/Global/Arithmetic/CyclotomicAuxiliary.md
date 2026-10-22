# Auxiliary cyclotomic extensions of number fields

This module builds two auxiliary extensions of a number field `F` from one prime number.
They live inside the cyclotomic field `F(ζ_q)`. The first is a cyclic extension of `F` of
any given degree `n > 0`. The second is `F(ζ_q)` itself, a Galois extension of `F` with a
finite place whose ramification index is divisible by `n`. Both lie in the universe of
`F`, as the predicates of `Langlands.ClassField.Global.FundamentalClassStatement` require.
The uniqueness of global fundamental classes uses the second (module
`Langlands.ClassField.Global.FundamentalClassProof`). Artin–Tate's uniqueness argument
uses a cyclic extension of the given degree instead, the first result here.

## Definition

- `auxiliaryPrime F n : ℕ` is a prime `q` with `q ≡ 1 (mod max n 1 · [F : ℚ]!)`. It is
  chosen with `Classical.choose` from Mathlib's `Nat.exists_prime_gt_modEq_one`
  (Dirichlet's theorem for primes `≡ 1` modulo a given modulus). The choice is not
  canonical. The `max n 1` only makes the modulus nonzero; for `n > 0` the modulus is
  `n · [F : ℚ]!`.

## Theorems

- `auxiliaryPrime_prime F n`: `auxiliaryPrime F n` is prime.
- `dvd_auxiliaryPrime_sub_one F (hn : 0 < n)`: `n · [F : ℚ]!` divides `q - 1`, where
  `q = auxiliaryPrime F n`.
- `intermediateField_numberField`: an intermediate field of an extension of number
  fields is a number field (characteristic zero, finite over `ℚ` through `F`).
- `dvd_finrank_cyclotomicField F q`: for a prime `q`, `q - 1` divides
  `[F : ℚ] · [F(ζ_q) : F]`. Here `F(ζ_q)` is Mathlib's `CyclotomicField q F`. For a
  primitive `q`-th root of unity `ζ`, `[ℚ(ζ) : ℚ] = deg Φ_q = q - 1`
  (`Polynomial.cyclotomic_eq_minpoly_rat`, `IntermediateField.adjoin.finrank`). This
  degree divides `[F(ζ_q) : ℚ] = [F : ℚ] [F(ζ_q) : F]`.
- `exists_cyclic_extension F (hn : 0 < n)`: there are a number field `K : Type u`, an
  `F`-algebra structure on `K`, `IsGalois F K`, `IsCyclic (K ≃ₐ[F] K)` and
  `Module.finrank F K = n`.
- `ramificationIdx_int_le_finrank q P`: for a rational prime `q` and a prime `P` of `𝓞 F`
  over `q`, `e(P|q) ≤ [F : ℚ]`.
- `sub_one_dvd_ramificationIdx q hζ P`: if a number field `K` contains a primitive `q`-th
  root of unity `ζ`, then every prime `P` of `𝓞 K` over `q` has `q - 1 ∣ e(P|q)`.
- `exists_galois_ramified F n (hn : 0 < n)`: there are a number field `K : Type u`, an
  `F`-algebra structure on `K`, `IsGalois F K`, and Mathlib height-one primes `v` of
  `𝓞 F` and `w` of `𝓞 K` with `w.asIdeal.LiesOver v.asIdeal` and
  `n ∣ w.asIdeal.ramificationIdx (𝓞 F)`. Mathlib's `ramificationIdx` is taken over the
  base ring `𝓞 F` at the prime under `w`, which is `v`.

## Proofs

Throughout, `d = [F : ℚ]`, `q = auxiliaryPrime F n` and `M = F(ζ_q)`. The field `M` is
Galois over `F` (`IsCyclotomicExtension.isGalois`).

Cyclic extension.

1. `Gal(M/F)` is cyclic. `IsPrimitiveRoot.autToPow` embeds it into `(ℤ/qℤ)ˣ`
   (`autToPow_injective`), which is cyclic for prime `q`
   (`ZMod.isCyclic_units_prime`).
2. `n` divides `[M : F]`. We have `n d ∣ n · d! ∣ q - 1 ∣ d [M : F]`
   (`dvd_finrank_cyclotomicField`); cancel `d > 0`.
3. Let `g` generate `Gal(M/F)`, of order `[M : F]`, and let `H` be the subgroup generated
   by `g^n`. It has order `[M : F] / n` (`orderOf_pow_of_dvd`) and is normal because the
   group is commutative. Its fixed field `K` has `[M : K] = |H|`
   (`IntermediateField.finrank_fixedField_eq_card`), hence `[K : F] = n`. `K / F` is
   Galois (`IsGalois.of_fixedField_normal_subgroup`), and `Gal(K/F)` is cyclic as the
   image of the surjective restriction `AlgEquiv.restrictNormalHom`.

The classical argument takes `q` unramified in `F`, so that `F` and `ℚ(ζ_q)` are linearly
disjoint and `[M : F] = q - 1`. Step 2 avoids this: the congruence on `q` makes `[M : F]`
divisible by `n` whatever `F ∩ ℚ(ζ_q)` is.

Ramified place.

1. `ramificationIdx_int_le_finrank`: Mathlib's fundamental identity
   `Ideal.sum_ramification_inertia_eq_finrank` gives `Σ_{P | q} e(P|q) f(P|q) = d`, and
   `f(P|q) ≥ 1` (`Ideal.inertiaDeg_pos`).
2. `sub_one_dvd_ramificationIdx`: let `P₀ = P ∩ 𝓞 ℚ(ζ)`. Mathlib's
   `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime` gives `e(P₀|q) = q - 1`, and
   ramification indices multiply in `ℤ ⊆ 𝓞 ℚ(ζ) ⊆ 𝓞 K` (`Ideal.ramificationIdx_tower`).
3. `exists_galois_ramified`: choose a prime `Q` of `𝓞 M` over `q`
   (`Ideal.nonempty_primesOver`) and set `P = Q ∩ 𝓞 F`. Then `e(Q|q) = e(P|q) e(Q|P)`.
   Here `n · d!` divides `q - 1`, which divides `e(Q|q)`. Also `0 < e(P|q) ≤ d`, so
   `e(P|q)` divides `d!`. Hence `n · d!` divides `d! · e(Q|P)`, and `n` divides
   `e(Q|P)`.

Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used.

## Provenance

Derived. Artin and Tate use the existence of cyclic cyclotomic extensions of every degree
in their construction of the global fundamental classes: E. Artin and J. Tate, *Class
Field Theory* (2009), registered as `artin-tate-2009-class-field-theory`, Chapter VII §3,
the Proposition on printed p.46 and the first paragraph of printed p.50 (PDF page =
printed page + 9). The degree argument above (`q ≡ 1 (mod n · d!)` instead of `q`
unramified in `F`) and the ramified variant are internal to this formalization. They rest
on Mathlib's Dirichlet theorem for primes `≡ 1 (mod k)` and on Mathlib's total ramification
of `q` in `ℚ(ζ_q)` (Washington, *Introduction to Cyclotomic Fields*, Lemma 1.4).
