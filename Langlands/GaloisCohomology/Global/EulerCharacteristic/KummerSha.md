# `Ш²` of the roots of unity

`Langlands/GaloisCohomology/Global/EulerCharacteristic/KummerSha.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `S` a finite set of finite places containing the places above a prime
`ℓ`, and `μ_ℓ = μ_ℓ(K_S)`. A class `x ∈ H²(G_S, μ_ℓ)` lies in `Ш²_S(μ_ℓ)` exactly when its image in
`H²(G_S, 𝒪_Sˣ)` vanishes (`mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero`), provided `ℓ` is odd
or `K` is totally complex. In one direction, the image of `x` in the Brauer group of `K` is locally
trivial at the places of `S` (local Kummer theory: `H²(K_v, μ_ℓ) → Br(K_v)` is injective,
`injective_coeffMap_rootsOfUnityLocalHom_two` of `Langlands.GaloisCohomology.Global.PoitouTate.Trace`, by
Hilbert 90), outside `S` (it comes from the
`S`-units) and at the infinite places, hence zero (Hasse); the image in `H²(G_S, 𝒪_Sˣ)` is killed by
`ℓ` and is zero in the Brauer group, hence zero. In the other direction the localizations of `x` at
the places of `S` vanish by the same injectivity, and at the real places `H²(K_w, μ_ℓ) = 0` for `ℓ`
odd. By the Kummer sequence of the `S`-units, `Ш²_S(μ_ℓ)` is the image of the connecting map
`H¹(G_S, 𝒪_Sˣ) → H²(G_S, μ_ℓ)` (`mem_sha_iff_exists_δ`).

```lean
theorem mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero (hN : N.Prime)
    (hK : N ≠ 2 ∨ IsTotallyComplex K) (x : cohomology (dualizingModule K Ω S N) 2) :
    x ∈ sha ι (dualizingModule K Ω S N) 2 ↔
      (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) N) 2).hom x = 0
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [inst_5 : NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) →
    Nat.Prime N →
      N ≠ 2 ∨ NumberField.IsTotallyComplex K →
        ∀
          (x :
            ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
                2)),
          x ∈ Langlands.GaloisCohomology.sha ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2 ↔
            (ModuleCat.Hom.hom
                  (Langlands.ProfiniteCohomology.coeffMap
                    (Langlands.GaloisCohomology.rootsOfUnityToSUnits S
                      (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) N)
                    2))
                x =
              0
```

## Outline of the proofs

Local Kummer theory (`localKummerSequence`, `injective_coeffMap_rootsOfUnityLocalHom_two` of `Langlands.GaloisCohomology.Global.PoitouTate.Trace`): the sequence `0 → μ_N(K_S) → K̄_vˣ → K̄_vˣ → 0` over `G_{K_v}` is short exact, and `H¹(K_v, K̄_vˣ) = 0` (Hilbert 90). Globally, the image of `x` in the Brauer group is the inflation of its image in `H²(G_S, 𝒪_Sˣ)` (`brauerClass_eq_maximalSUnitsInflation`); it is locally trivial at every place exactly when the localizations of `x` vanish at `S` and the real places, and the Hasse principle and the injectivity of `H²(G_S, 𝒪_Sˣ)[ℓ] → Br(K)` conclude.

- `mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero`: **`Ш²` of `μ_ℓ` and the `S`-units.** For a prime `N = ℓ` which is odd or with `K` totally complex, a class of `H²(G_S, μ_ℓ)` lies in `Ш²_S(μ_ℓ)` exactly when its image in `H²(G_S, 𝒪_Sˣ)` vanishes.

## Declarations

`mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 506 ((iii): Ш and the S-class group), (8.3.4), p. 453.
- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. ICM Stockholm 1962, Theorem 3.1, p. 291.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/KummerSha.lean` lines 1–155. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `mem_ptSha_iff_cohomologyMap_eq_zero` → `mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero`.
