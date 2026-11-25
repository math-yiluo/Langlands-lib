# Tate's base case: assembly

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/Base.lean`, namespace `Langlands.GaloisCohomology`.

In the situation of Tate's base case (`L ⊆ K_S` Galois over `K` of degree prime to `ℓ`, `μ_ℓ ⊆ L`,
`ℓ` odd or `L` totally complex, `M` killed by `ℓ` and trivial on `G_S(L)`), the formula
`globalEulerRatio ι M = 1` follows from the computations of the preceding files and the count of
`H²(G_S, M)` given by the nine-term sequence of Poitou–Tate, once `#Ш²_S(M) = ℓ^{d(A₁/ℓ)}`
(`baseCase_globalEulerRatio_of_card_sha`). With `d(X) = dim (X ⊗ Hom(μ_ℓ, M))^{Gal(L/K)}` and
`Aᵢ = Hⁱ(G_S(L), 𝒪_Sˣ)`, Tate's computation reads

`h⁰ - h¹ + h² = d(A₀[ℓ]) - d(A₀/ℓ) - d(A₁[ℓ]) + (#Ш² + ∑_{v ∈ S} h²(K_v) - h⁰(M'))
             = -(d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)) + d(A₁/ℓ) - d(A₁[ℓ]) + d(𝔽_ℓ[S_L]) - d(𝔽_ℓ)
             = -d(𝔽_ℓ[∞_L]) = ∑_{w real} h⁰(K_w, M) - #∞ · dim M.`

```lean
theorem baseCase_globalEulerRatio_of_card_sha
    (hc : ℓ ≠ 2 ∨ IsTotallyComplex L) (s : ℕ) (hsha : Nat.card (sha ι M 2) = ℓ ^ s)
    (hs : (s : ℤ) = baseShaExponent hL hcop hζ M hMℓ hMP) :
    globalEulerRatio ι M = 1
def ShaTwoBaseCountStatement : Prop
theorem globalEulerCharacteristicBase_of_shaTwoBaseCount
    (hsha : ShaTwoBaseCountStatement.{u}) : GlobalEulerCharacteristicBaseStatement.{u}
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.baseCase_globalEulerRatio_of_card_sha : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S] {ℓ : ℕ}
  [inst_6 : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ {L : Type u} [inst_7 : Field L] [inst_8 : NumberField L] [inst_9 : Algebra K L] [inst_10 : Algebra L Ω]
      [inst_11 : IsScalarTower K L Ω]
      (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_12 : IsGalois K L]
      [inst_13 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
      (hcop : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).index.Coprime ℓ)
      (hζ : ∃ ζ, IsPrimitiveRoot ζ ℓ)
      (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_14 : Langlands.IsSmoothRep M] [inst_15 : Finite ↑M] (hMℓ : ∀ (m : ↑M), ℓ • m = 0)
      (hMP : ∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1)
      (ι : Langlands.Galois.PlaceEmbeddings K Ω),
      ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L →
        ∀ (s : ℕ),
          Nat.card ↥(Langlands.GaloisCohomology.sha ι M 2) = ℓ ^ s →
            ↑s = Langlands.GaloisCohomology.baseShaExponent hL hcop hζ M hMℓ hMP →
              Langlands.GaloisCohomology.globalEulerRatio ι M = 1
@Langlands.GaloisCohomology.ShaTwoBaseCountStatement : Prop
@Langlands.GaloisCohomology.globalEulerCharacteristicBase_of_shaTwoBaseCount : Langlands.GaloisCohomology.ShaTwoBaseCountStatement →
  Langlands.GaloisCohomology.GlobalEulerCharacteristicBaseStatement
```

## Outline of the proofs

Assemble: Poitou–Tate (`card_cohomology_two_mul_card_dual_zero`) gives `h2 + h0(M') = sha + Σ_v h2(K_v)` (the real `H²` vanish since `ℓ` is odd or `K` totally complex); `BaseDegrees`, `BaseLocal`, `PlaceCount`, `InfiniteCount`, `RealCount` express every term by `d`; with `sha = d(A₁/ℓ)` (`ShaTwoBaseCountStatement`) the alternating sum is `Σ_{w real} log #H⁰(K_w, M) − #∞ · log #M`, which is the formula.

- `baseCase_globalEulerRatio_of_card_sha`: **Tate's base case from the count of `Ш²`.** If `#Ш²_S(M) = ℓ^s` with `s = d(A₁/ℓ)`, the global Euler characteristic formula holds for `M`.
- `ShaTwoBaseCountStatement`: **The count of `Ш²` in Tate's base case**: in the situation of the base case, with `L / K` Galois, `#Ш²_S(M) = ℓ^s` for `s = d(A₁/ℓ)` (`baseShaExponent`), `A₁ = H¹(G_S(L), 𝒪_Sˣ)`.
- `globalEulerCharacteristicBase_of_shaTwoBaseCount`: **Tate's base case** from the nine-term sequence of Poitou–Tate and the count of `Ш²`.

## Declarations

`div_eq_div_of_exponents`, `odd_or_isTotallyComplex`, `card_cohomology_two_realLocalModule_eq_one`, `baseTwistFun_quotient`, `baseTwistFun_one`, `baseShaExponent`, `baseCase_globalEulerRatio_of_card_sha`, `ShaTwoBaseCountStatement`, `globalEulerCharacteristicBase_of_shaTwoBaseCount`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), pp. 506–507 (the case A = μ_p and its twists).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §5, Theorem 5.1, p. 67.
