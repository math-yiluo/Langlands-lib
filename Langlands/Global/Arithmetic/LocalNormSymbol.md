# The cyclotomic symbol of local norms lies in the Galois image

Let `L / K` be a Galois extension of number fields, and let `ζ ∈ L` be a primitive `m`-th
root of unity, `m ≠ 0`. Let `w` be a finite place of `K` above the place `p₀` of `ℚ`, and
`p` the corresponding prime. This module proves the Artin–Tate norm theorem: for every
`b ∈ K_wˣ`, the explicit cyclotomic symbol `σ_p(N_{K_w/ℚ_p}(b)) ∈ (ℤ/m)ˣ` lies in the image
of `Gal(L/K)` acting on `ζ`. This is the key step relating the explicit symbols to
Galois groups in the reciprocity proof for cyclic cyclotomic extensions (task fb66219f).
All declarations are in the namespace `Langlands.Global.CyclotomicSymbol`.

## Definitions

- `fact_prime_primes`: the instance `Fact (p : ℕ).Prime` for `p : Nat.Primes`.
- `normSymbolAt m p₀ w : (w.adicCompletion K)ˣ →* (ZMod m)ˣ`, for a place `w` of `K` with
  `w.asIdeal.LiesOver p₀.asIdeal`. It sends `b` to
  `localSymbol m p (padicEquiv p₀ (localNorm p₀ w b))`, where:
  - `localNorm p₀ w = Algebra.norm (p₀.adicCompletion ℚ)` on `w.adicCompletion K` is the
    Library's local norm (`Langlands.Global.AdelicFunctoriality.FiniteExtension`);
  - `padicEquiv p₀ : p₀.adicCompletion ℚ ≃A[ℚ] ℚ_p` is Mathlib's comparison;
  - `localSymbol` is the explicit symbol of `Langlands.Global.Arithmetic.CyclotomicSymbol`.

  The base place `p₀` is a parameter, so that the places above a fixed `p₀` can be
  compared directly.

## Theorems

- `exists_nhds_normSymbolAt_eq_one`: the symbol is trivial on a neighborhood of `1`. The
  local norm and `padicEquiv` are continuous, so `‖N(b) − 1‖` is small near `b = 1`, and
  `localSymbol_eq_one` applies.
- `exists_pow_sub_mem_imp_mem`: if `z ∈ 𝓞 K` and `V` is a neighborhood of `z` in `K_w`, then
  every `y ∈ 𝓞 K` with `y − z ∈ w^N` lies in `V`, for some `N`. The proof uses the valuation
  basis of the topology (`Valued.mem_nhds`) and
  `v(y − z) ≤ exp(−N) ⇔ y − z ∈ w^N` (`intValuation_le_pow_iff_mem`).
- `prod_localNorm_algebraMap`: for `α ∈ K`, the product of the local norms of `α` over the
  places above `p₀` is `N_{K/ℚ}(α)` in `ℚ_{p₀}`. This is the finite component of the
  Library's `normCompatibility` (principal adeles).
- `ratLocalSymbol_norm_eq_prod`: the symbol at `p` of `N_{K/ℚ}(α)` is the product over the
  places `w | p₀` of `normSymbolAt m p₀ w (α)`.
- `natCast_not_mem_of_coprime`: an integer `M` prime to `p` does not lie in a prime of
  `𝓞 K` above `p₀`.
- `exists_crt`: Chinese remainder approximation (`Ideal.exists_forall_sub_mem_ideal`). For
  `β ∈ 𝓞 K`, `N` and `M` prime to `p`, some `α ∈ 𝓞 K` satisfies `α ≡ β mod w^N`,
  `α ≡ 1 mod w'^N` for the other places `w' | p₀`, and `α ≡ 1 mod M`.
- `symbolProduct_eq_mul`: the product of all local symbols is the product of the factors in
  a finite set `S` times `outsideSymbol m S`.
- `primeSymbol_norm_eq_one`: let `ℓ ≠ p` be a prime dividing `m`, and let `α ∈ 𝓞 K` with
  `α ≡ 1 mod m₀²`, where `m₀` is the prime-to-`p` part of `m`. Then the symbol at `ℓ` of
  `N(α)` is `1`.
- `normSymbolAt_integral_mem`: the theorem for `b = β ∈ 𝓞 K` nonzero at `w`.
  1. Use `exists_nhds_normSymbolAt_eq_one` and `exists_pow_sub_mem_imp_mem` to choose `N`
     so large that, for `α ∈ 𝓞 K`, the congruences `α ≡ β mod w^N` and `α ≡ 1 mod w'^N` give
     `normSymbolAt w α = normSymbolAt w β` and `normSymbolAt w' α = 1`.
  2. Take `α` from `exists_crt` with `M = m₀²`.
  3. Replace `α` by `α' = α + kT`. Here `T = M · N(∏ w'^N)` is a positive integer in all the
     ideals, and `k` is chosen with `N_{K/ℚ}(α') > 0` (`exists_norm_add_nsmul_pos`).
  4. Apply the product formula to `N(α') ∈ ℚˣ` and split it with
     `S = {primes dividing m·p}`:
     - the sign is `1`;
     - the factors at `ℓ ∈ S`, `ℓ ≠ p`, are `1` (`primeSymbol_norm_eq_one`);
     - the factor at `p` equals `normSymbolAt w β` (`ratLocalSymbol_norm_eq_prod` and
       step 1);
     - the product outside `S` is evaluated at `N(α') = N(α'𝓞)`, an ideal norm, so it lies
       in the Galois image (`outsideSymbol_absNorm_mem`).

     Hence `normSymbolAt w β` is the inverse of an element of the Galois image.
- `normSymbolAt_mem_galoisImage` (the Artin–Tate norm theorem): for every
  `b ∈ (w.adicCompletion K)ˣ`, `normSymbolAt m p₀ w b ∈ galoisImage K hζ`. The symbol is
  constant near `b`, and `K` is dense in `K_w` (`HeightOneSpectrum.denseRange_algebraMap`),
  so `b` may be replaced by some `y ∈ Kˣ`. Writing `y = a / d` with `a, d ∈ 𝓞 K`
  (`IsFractionRing.div_surjective`) reduces to the integral case.

## Sources and provenance

Artin–Tate, Chapter VII §2, Theorem 2 (printed p.39, PDF p.48): for `K ⊆ ℚ(ζ)` and an idele
`a ∈ ℚˣ N_{K/ℚ} J_K`, `σ(a)` lies in the subgroup fixing `K`. The local consequence is
Theorem 3 (printed p.40, PDF p.49): a local norm from `K_p` has `σ_p` in the subgroup
determining `K_p`. Their proof has three ingredients: the continuity of `σ_p`, weak
approximation, and the Frobenius at unramified primes.

This module proves the analogous statement over an arbitrary number field `K`, with `L / K`
Galois containing `ζ`. Provenance is derived. Several choices are internal.

- The Galois image is used in place of the subfield of `ℚ(ζ)`.
- The unramified primes are handled through ideal norms (module `FrobeniusNormClass`).
- Positivity of the global norm replaces approximation at the real places (module
  `NormCongruence`).
- The other places above `p` are handled by a Chinese remainder argument with the Library's
  principal norm compatibility.
