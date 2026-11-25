# The global Euler characteristic formula: proof

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Proof.lean`, namespace `Langlands.GaloisCohomology`.

Tate's global Euler characteristic formula `GlobalEulerCharacteristicStatement`, for every finite
module, and its `ℓ`-primary case. The degree-three case of Tate's theorem on the real places, which
the multiplicativity of the ratio uses (`globalEulerRatio_shortExact`), is
`realLocalizationDegreeThreeStatement` of
`Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof`; the base case uses the nine-term
sequence of Poitou–Tate (`poitouTateNineTermStatement`, through
`card_cohomology_two_mul_card_dual_zero`) and the count of `Ш²` (`shaTwoBaseCount`).

```lean
theorem eulerCharacteristic_eq_of_primary
    {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    {r : ℕ} (hr : ∀ m : M, (ℓ ^ r) • m = 0) :
    eulerCharacteristic M =
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)) /
        (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K)
theorem globalEulerCharacteristic : GlobalEulerCharacteristicStatement.{u}
theorem card_cohomology_one_mul_prod
    {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Nat.card (cohomology M 1) * ∏ w : {w : InfinitePlace K // w.IsReal},
        Nat.card (cohomology (realLocalModule ι M w.1) 0) =
      Nat.card (cohomology M 0) * Nat.card (cohomology M 2) *
        Nat.card M ^ Fintype.card (InfinitePlace K)
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.eulerCharacteristic_eq_of_primary : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
        [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M] {r : ℕ},
        (∀ (m : ↑M), ℓ ^ r • m = 0) →
          Langlands.ProfiniteCohomology.eulerCharacteristic M =
            (∏ w,
                ↑(Nat.card
                    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w)
                        0))) /
              ↑(Nat.card ↑M) ^ Fintype.card (NumberField.InfinitePlace K)
@Langlands.GaloisCohomology.globalEulerCharacteristic : Langlands.GaloisCohomology.GlobalEulerCharacteristicStatement
@Langlands.GaloisCohomology.card_cohomology_one_mul_prod : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S) →
    Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 1) *
        ∏ w,
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 0) =
      Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 0) *
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 2) *
        Nat.card ↑M ^ Fintype.card (NumberField.InfinitePlace K)
```

## Outline of the proofs

The formula is `globalEulerRatio ι M = 1` (`globalEulerRatio_eq_one_iff`); `globalEulerRatio_eq_one_of_base` proves it for every finite module from the base case and the real places in degree three. The degree-three statement, which the multiplicativity of the ratio uses (`globalEulerRatio_shortExact`), is `realLocalizationDegreeThreeStatement` (`Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof`), and the base case is `globalEulerCharacteristicBase_of_shaTwoBaseCount` with `shaTwoBaseCount`.

- `eulerCharacteristic_eq_of_primary`: **The `ℓ`-primary case** of the global Euler characteristic formula: for a prime `ℓ` with the places above `ℓ` in `S` and a finite smooth `G_S`-module killed by a power of `ℓ`.
- `globalEulerCharacteristic`: **Tate's global Euler characteristic formula** for every finite module.
- `card_cohomology_one_mul_prod`: **The order of `H¹(G_S, M)`** (from the global Euler characteristic formula): for every finite smooth `G_S`-module `M` with the places above `#M` in `S`, `#H¹(G_S, M) · ∏_{w real} #H⁰(K_w, M) = #H⁰(G_S, M) · #H²(G_S, M) · (#M)^{[K : ℚ]_∞}`, the exponent being the number of infinite places of `K`.

## Declarations

`eulerCharacteristic_eq_of_primary`, `globalEulerCharacteristic`, `card_cohomology_one_mul_prod`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.7.4), p. 505, proof pp. 506–509.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §5, Theorem 5.1, p. 67 (and its proof, pp. 68–72).
- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. ICM Stockholm 1962, pp. 291–292 (the count for finite S).
