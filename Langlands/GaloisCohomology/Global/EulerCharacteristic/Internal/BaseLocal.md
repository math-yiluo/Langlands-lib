# The dual module and the local terms in Tate's base case: the counts

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/BaseLocal.lean`, namespace `Langlands.GaloisCohomology`.

In the situation of `BaseDegrees.lean`, with `N = Hom(μ_ℓ, M)` as a representation of
`Γ = Gal(L/K)` (`twistRep`) and `D_v ⊆ Γ` the decomposition group at a finite place `v`:

* `#H⁰(G_S, M') = ℓ^{dim N^Γ}` for `M' = Hom(M, μ_ℓ)` (`baseCase_card_dual_zero`);
* `#H²(K_v, M) = ℓ^{dim N^{D_v}}` (`baseCase_card_local_two`), through local duality
  `#H²(K_v, M) = #H⁰(K_v, M^∨)` with the Cartier dual `M^∨ = Hom(M, K̄_vˣ)`, whose invariants are the
  `G_{K_v}`-homomorphisms `M → μ_ℓ(K̄_v) ≅ μ_ℓ(K_S)` (`homEquivLocalUnits`).

```lean
theorem baseCase_card_dual_zero :
    Nat.card (cohomology (PoitouTate.dual ℓ M) 0) =
      ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (baseTwistRep hL hζ M hMℓ hMP).invariants
theorem baseCase_card_local_two (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (cohomology (localModule ι M v) 2) =
      ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants
        ((baseTwistRep hL hζ M hMℓ hMP).comp (decompositionGroup hL ι v).subtype))
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.baseCase_card_dual_zero : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : ℕ} [inst_5 : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ {L : Type u} [inst_6 : Field L] [inst_7 : NumberField L] [inst_8 : Algebra K L] [inst_9 : Algebra L Ω]
      [inst_10 : IsScalarTower K L Ω]
      (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_11 : IsGalois K L]
      [inst_12 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal],
      (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).index.Coprime ℓ →
        ∀ (hζ : ∃ (ζ : L), IsPrimitiveRoot ζ ℓ)
          (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
          [inst_13 : Langlands.IsSmoothRep M] [inst_14 : Finite ↑M] (hMℓ : ∀ (m : ↑M), ℓ • m = 0)
          (hMP : ∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1),
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual ℓ M) 0) =
            ℓ ^
              Module.finrank (ULift.{u, 0} (ZMod ℓ))
                ↥(Langlands.GaloisCohomology.baseTwistRep hL hζ M hMℓ hMP).invariants
@Langlands.GaloisCohomology.baseCase_card_local_two : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : ℕ} [inst_5 : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ {L : Type u} [inst_6 : Field L] [inst_7 : NumberField L] [inst_8 : Algebra K L] [inst_9 : Algebra L Ω]
      [inst_10 : IsScalarTower K L Ω]
      (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_11 : IsGalois K L]
      [inst_12 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal],
      (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).index.Coprime ℓ →
        ∀ (hζ : ∃ (ζ : L), IsPrimitiveRoot ζ ℓ)
          (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
          [inst_13 : Langlands.IsSmoothRep M] [Finite ↑M] (hMℓ : ∀ (m : ↑M), ℓ • m = 0)
          (hMP : ∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1)
          (ι : Langlands.Galois.PlaceEmbeddings K Ω)
          (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M v) 2) =
            ℓ ^
              Module.finrank (ULift.{u, 0} (ZMod ℓ))
                ↥(Representation.invariants
                    (MonoidHom.comp (Langlands.GaloisCohomology.baseTwistRep hL hζ M hMℓ hMP)
                      (Langlands.GaloisCohomology.decompositionGroup hL ι v).subtype))
```

## Outline of the proofs

`H⁰(G_S, M') = Hom_{G_S}(M, μ_ℓ)` and `LocalCount` give the global term. At a finite place, local duality identifies `H²(K_v, M)` with the dual of `H⁰(K_v, M^∨)`, `M^∨` the Cartier dual, and `H⁰(K_v, M^∨) = Hom_{G_v}(M, K̄_vˣ) = Hom_{G_v}(M, μ_ℓ(K_S))` because `ι_v` maps `μ_ℓ(K_S)` onto the `ℓ`-torsion of `K̄_vˣ`.

- `baseCase_card_dual_zero`: **The dual module.** `#H⁰(G_S, M') = ℓ^{dim N^Γ}` for `M' = Hom(M, μ_ℓ)`.
- `baseCase_card_local_two`: **The local terms.** `#H²(K_v, M) = ℓ^{dim N^{D_v}}` at a finite place `v`.

## Declarations

`finite_rootsOfUnityModule_maximal`, `baseTwistRep`, `quotHom_quotientGalEquiv`, `baseCase_card_dual_zero`, `comp_rootsOfUnityLocalHom_bijective`, `baseCase_card_local_two`.

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. ICM Stockholm 1962, Theorem 2.1, p. 289 (local duality).
- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 506 ((iii)).
