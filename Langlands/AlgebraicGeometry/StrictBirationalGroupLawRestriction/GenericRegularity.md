# Generic regularity of a nonzerodivisor modulo extended ideals

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.GenericRegularity`
proves two results of commutative algebra. They are derived results used in the Library's proof
`Langlands.AlgebraicGeometry.strictBirationalGroupLawRestriction` of Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §5.2 Proposition 2 (printed p. 115; literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`). In BLR's proof (printed p. 116) the set of
points over which an `S`-dense open of `X ×_S X` fails to be fibrewise dense is shown to be
constructible (BLR 2.5/1, EGA IV 9.5.3). The second result below gives, by generic flatness, the
local form of that statement which the Library's proof uses instead.

## `exists_pow_mul_mem_map_of_mul_mem_map`

```lean
theorem exists_pow_mul_mem_map_of_mul_mem_map {D B : Type u} [CommRing D] [IsDomain D]
    [IsNoetherianRing D] [CommRing B] [Algebra D B] [Algebra.FiniteType D B]
    {h : B} (hh : h ∈ nonZeroDivisors B) :
    ∃ d : D, d ≠ 0 ∧ ∀ (𝔭 : Ideal D) (y : B), h * y ∈ 𝔭.map (algebraMap D B) →
      ∃ k : ℕ, algebraMap D B d ^ k * y ∈ 𝔭.map (algebraMap D B)
```

Let `B` be a finitely generated algebra over a noetherian domain `D` and `h` a nonzerodivisor of
`B`. Then there is `d ≠ 0` in `D` such that, for every ideal `𝔭` of `D`, multiplication by `h` is
injective on `B_d / 𝔭 B_d`; elementwise, `h y ∈ 𝔭 B` implies `d^k y ∈ 𝔭 B` for some `k`.

Proof. Generic flatness, `Module.Flat.exists_ne_zero_flat_localization_tensorProduct` (module
`Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct`),
applied to the `B`-module `M = B ⧸ (h)` gives `d ≠ 0` with `N ⊗_B M` flat over `D`, where
`N = B_d` is the localization at the powers of `d`. The `D`-linear maps
`f : N → N`, `n ↦ h n`, and `g : N → N ⊗_B M`, `n ↦ n ⊗ 1`, form a short exact sequence:
`f` is injective because `h` is a nonzerodivisor of `B`, and `N ⊗_B M ≅ N ⧸ hN`
(`TensorProduct.tensorQuotEquivQuotSMul`) identifies `g` with the quotient map. Since the
cokernel is flat, `f ⊗ (D ⧸ 𝔭)` is injective
(`Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat`, module
`Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat`).
Through `(D ⧸ 𝔭) ⊗_D N ≅ N ⧸ 𝔭 N` (`TensorProduct.quotTensorEquivQuotSMul`) and
`𝔭 • N = 𝔭 N` (`Ideal.smul_top_eq_map`), the relation `h y ∈ 𝔭 B` gives `y ∈ 𝔭 B_d`, and clearing
denominators in the localization gives `d^k y ∈ 𝔭 B`.

## `exists_notMem_forall_minimal_mem`

```lean
theorem exists_notMem_forall_minimal_mem {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
    [IsNoetherianRing A] [Algebra.Smooth A T] (P : Ideal A) [P.IsPrime]
    (Z : Set (PrimeSpectrum T)) (hZ : IsOpen Z)
    (hP : ∀ Q : PrimeSpectrum T, Q.asIdeal.comap (algebraMap A T) = P →
      (∀ Q' : PrimeSpectrum T, Q' ≤ Q → Q'.asIdeal.comap (algebraMap A T) = P → Q' = Q) →
        Q ∈ Z) :
    ∃ a : A, a ∉ P ∧ ∀ Q : PrimeSpectrum T, P ≤ Q.asIdeal.comap (algebraMap A T) →
      a ∉ Q.asIdeal.comap (algebraMap A T) →
      (∀ Q' : PrimeSpectrum T, Q' ≤ Q →
        Q'.asIdeal.comap (algebraMap A T) = Q.asIdeal.comap (algebraMap A T) → Q' = Q) →
      Q ∈ Z
```

Let `T` be a smooth algebra over a noetherian ring `A`, `P` a prime of `A` and `Z` an open subset
of `Spec T`. Suppose `Z` contains every prime of `T` that is minimal among the primes lying over
`P`, that is, every generic point of an irreducible component of the fibre of `Spec T → Spec A`
over `P`. Then there is `a ∉ P` such that, for every prime `p ⊇ P` of `A` with `a ∉ p`, `Z`
contains every prime of `T` minimal among the primes lying over `p`. Geometrically: the generic
points of the fibres over the specializations of `P` in the basic open `D(a)` lie in `Z`.

Proof. Let `I` be the vanishing ideal of the closed set `Spec T \ Z`, so that `Q ∈ Z` exactly
when `I ⊄ Q`. Put `D = A ⧸ P` and `B = T ⧸ P T`. Through
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, `B ≅ D ⊗_A T` is smooth, flat and of finite
type over `D`, hence noetherian, and reduced by
`Langlands.AlgebraicGeometry.SmoothReducedBase.isReduced_of_smooth`.

1. Each minimal prime `𝔮` of `B` lies over the zero ideal of `D`: a nonzero element of `D` acts
   injectively on the flat `D`-module `B` (`Module.Flat.isSMulRegular_of_nonZeroDivisors`),
   while elements of minimal primes are zero divisors
   (`Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes`). So the preimage of `𝔮` in `T` is
   minimal among the primes lying over `P`, it lies in `Z` by hypothesis, and the image of `I`
   in `B` is not contained in `𝔮`.
2. Prime avoidance (`Ideal.subset_union_prime`) over the finitely many minimal primes of `B`
   gives `h ∈ I` whose image `h̄` lies in no minimal prime. As `B` is reduced, the intersection
   of its minimal primes is zero, so `h̄` is a nonzerodivisor of `B`.
3. `exists_pow_mul_mem_map_of_mul_mem_map` for `D`, `B` and `h̄` gives `d ≠ 0`; let `a ∈ A` lift
   `d`, so `a ∉ P`.
4. Let `Q` be a prime of `T` over `p ⊇ P` with `a ∉ p`, minimal among the primes over `p`, and
   suppose `I ⊆ Q`, so `h ∈ Q`. Then `Q` is a minimal prime of `J = p T`. In `T_Q` the radical
   of `J T_Q` is `Q T_Q` (`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`), so some
   `t h^n` with `t ∉ Q` lies in `J`. Take `n` least. Then `n ≥ 1`, and `h (t h^{n-1}) ∈ J`;
   passing to `B` and back, step 3 gives `a^k t h^{n-1} ∈ J` with `a^k t ∉ Q`, contradicting
   the minimality of `n`. Hence `I ⊄ Q`, that is, `Q ∈ Z`.

## Declarations used

From the Library: `Module.Flat.exists_ne_zero_flat_localization_tensorProduct`,
`Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat`,
`Langlands.AlgebraicGeometry.SmoothReducedBase.isReduced_of_smooth`. From Mathlib: the
localization, tensor product, quotient and minimal prime results named above.
