# The count of `Ш²` in Tate's base case

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/ShaCount.lean`, namespace `Langlands.GaloisCohomology`.

In the base case of Tate's computation (`L ⊆ K_S` Galois over `K` with group `Γ` of order prime to
the prime `ℓ`, `μ_ℓ ⊆ L`, `ℓ` odd or `L` totally complex, `M` killed by `ℓ` and trivial on
`P = G_S(L)`), `#Ш²_S(M) = ℓ^{d(A₁/ℓ)}` with `A₁ = H¹(P, 𝒪_Sˣ)` and `d(X) = dim (X ⊗ Hom(μ_ℓ, M))^Γ`
(`shaTwoBaseCount : ShaTwoBaseCountStatement`):

* `#Ш²_S(M) = ℓ^{dim Ш}` for the classes `Ш` of `H²(G_S, M)` over `𝔽_ℓ` vanishing at the places of
  `S` (`natCard_sha_two_eq_pow_finrank`; the real places impose nothing since `ℓ` is odd or `K` is
  totally complex);
* the Kummer map `A₁/ℓ → H²(P, μ_ℓ)` is injective and `Γ`-equivariant with image the classes
  vanishing on the Mackey family of `P` (`KummerShaOpen.lean`), so by the coprime twist
  (`finrank_shaSubmodule_eq_finrank_invariants`) `dim Ш = d(A₁/ℓ)`.

```lean
theorem natCard_sha_two_eq_pow_finrank (hK : Odd ℓ ∨ IsTotallyComplex K) :
    Nat.card (sha ι M 2) = ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ))
      (shaSubmodule (localFamily ι S) (zmodRepOfTorsion ℓ M hMℓ) 2)
theorem mem_shaSubmodule_mackey_iff_mem_range_kummerModNZMod (hc : ℓ ≠ 2 ∨ IsTotallyComplex L)
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ))) 2) :
    y ∈ shaSubmodule (mackeyFamily (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (localFamily ι S)) (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
          (nsmul_galRootsOfUnity_eq_zero ℓ))) 2 ↔
      y ∈ LinearMap.range (kummerModNZMod hS hL)
theorem finrank_shaSubmodule_two_eq_baseShaExponent (hc : ℓ ≠ 2 ∨ IsTotallyComplex L) :
    (Module.finrank (ULift.{u} (ZMod ℓ))
      (shaSubmodule (localFamily ι S) (zmodRepOfTorsion ℓ M hMℓ) 2) : ℤ) =
      baseShaExponent hL hcop hζ M hMℓ hMP
theorem shaTwoBaseCount : ShaTwoBaseCountStatement.{u}
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.natCard_sha_two_eq_pow_finrank : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S] {ℓ : ℕ}
  [inst_6 : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω)
      (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_7 : Langlands.IsSmoothRep M] [Finite ↑M] (hMℓ : ∀ (m : ↑M), ℓ • m = 0),
      Odd ℓ ∨ NumberField.IsTotallyComplex K →
        Nat.card ↥(Langlands.GaloisCohomology.sha ι M 2) =
          ℓ ^
            Module.finrank (ULift.{u, 0} (ZMod ℓ))
              ↥(Langlands.GaloisCohomology.shaSubmodule (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
                  (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ M hMℓ) 2)
@Langlands.GaloisCohomology.mem_shaSubmodule_mackey_iff_mem_range_kummerModNZMod : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : ℕ} [inst_5 : Fact (Nat.Prime ℓ)]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) {L : Type u}
  [inst_6 : Field L] [inst_7 : NumberField L] [inst_8 : Algebra K L] [inst_9 : Algebra L Ω]
  [inst_10 : IsScalarTower K L Ω] (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L →
    ∀
      (y :
        ↑(Langlands.ProfiniteCohomology.cohomology
            (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
              (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ
                (Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) ℓ)
                ⋯))
            2)),
      y ∈
          Langlands.GaloisCohomology.shaSubmodule
            (Langlands.GaloisCohomology.mackeyFamily
              (Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
              (Langlands.GaloisCohomology.PoitouTate.localFamily ι S))
            (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
              (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ
                (Langlands.GaloisCohomology.rootsOfUnityModule K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) ℓ)
                ⋯))
            2 ↔
        y ∈ (Langlands.GaloisCohomology.kummerModNZMod hS hL).range
@Langlands.GaloisCohomology.finrank_shaSubmodule_two_eq_baseShaExponent : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : ℕ} [inst_5 : Fact (Nat.Prime ℓ)],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
    ∀ {L : Type u} [inst_6 : Field L] [inst_7 : NumberField L] [inst_8 : Algebra K L] [inst_9 : Algebra L Ω]
      [inst_10 : IsScalarTower K L Ω]
      (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_11 : IsGalois K L]
      [inst_12 : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).Normal]
      (hcop : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).index.Coprime ℓ)
      (hζ : ∃ (ζ : L), IsPrimitiveRoot ζ ℓ) (ι : Langlands.Galois.PlaceEmbeddings K Ω)
      (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_13 : Langlands.IsSmoothRep M] [inst_14 : Finite ↑M] (hMℓ : ∀ (m : ↑M), ℓ • m = 0)
      (hMP : ∀ g ∈ ↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL), M.ρ g = 1),
      ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L →
        ↑(Module.finrank (ULift.{u, 0} (ZMod ℓ))
              ↥(Langlands.GaloisCohomology.shaSubmodule (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
                  (Langlands.ProfiniteCohomology.zmodRepOfTorsion ℓ M hMℓ) 2)) =
          Langlands.GaloisCohomology.baseShaExponent hL hcop hζ M hMℓ hMP
@Langlands.GaloisCohomology.shaTwoBaseCount : Langlands.GaloisCohomology.ShaTwoBaseCountStatement
```

## Outline of the proofs

Over `𝔽_ℓ`, `#Ш² = ℓ^{dim}`. The Kummer map `A₁/ℓ → H²(P, μ_ℓ)` is injective, `Γ`-equivariant and has image the classes vanishing on the Mackey family (`KummerShaOpen`), so `ShaTwist` gives `dim Ш = dim (A₁/ℓ ⊗ Hom(μ_ℓ, M))^Γ = d(A₁/ℓ)`, the invariants being compared along `G_S/P ≅ Gal(L/K)`.

- `natCard_sha_two_eq_pow_finrank`: **The order of `Ш²`.** If the real places impose nothing (`ℓ` odd or `K` totally complex), `#Ш²_S(M) = ℓ^{dim Ш}` for the classes `Ш` of `H²(G_S, M)` over `𝔽_ℓ` vanishing at the places of `S`.
- `mem_shaSubmodule_mackey_iff_mem_range_kummerModNZMod`: **The image of the Kummer map.** A class of `H²(P, μ_ℓ)` over `𝔽_ℓ` vanishes on the Mackey family of `P` exactly when it comes from `A₁/ℓ`.
- `finrank_shaSubmodule_two_eq_baseShaExponent`: **The dimension of `Ш²`.** The classes of `H²(G_S, M)` over `𝔽_ℓ` vanishing at the places of `S` have dimension `d(A₁/ℓ)` (`baseShaExponent`).
- `shaTwoBaseCount`: **The count of `Ш²` in the base case.**

## Declarations

`mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff`, `natCard_sha_two_eq_pow_finrank`, `kummerModNZMod`, `kummerModNZMod_mk`, `kummerModNZMod_injective`, `isIntertwiningMap_kummerModNZMod`, `mem_shaSubmodule_mackey_iff_mem_range_kummerModNZMod`, `finrank_shaSubmodule_two_eq_baseShaExponent`, `shaTwoBaseCount`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), pp. 506–508.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/MemShaSubmoduleCohomologyAddEquivOfEquivIff.lean` lines 1–216, `src/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/GaloisCohomologyRatios/FiniteCohomologyRootsZMod.lean` lines 86–93. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `natCard_ptSha_eq_pow_finrank` → `natCard_sha_two_eq_pow_finrank`, `kummerModNZMod_apply` → `kummerModNZMod_mk`, `mem_shaSubmodule_iff_mem_range_kummerModNZMod` → `mem_shaSubmodule_mackey_iff_mem_range_kummerModNZMod`, `finrank_shaSubmodule_two_eq_finrank_invariants` → `finrank_shaSubmodule_two_eq_baseShaExponent`, `natCard_ptSha_two_gs` → `natCard_sha_two_eq_pow_finrank`.
