# Counting `H²(G_S, M)` with Poitou–Tate

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Corollaries.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`
containing the places above `N ≥ 1`, and `M` a finite smooth `G_S`-module killed by `N`, with dual
`M' = Hom(M, μ_N)`. The end of the nine-term sequence of Poitou–Tate,
`H²(G_S, M) → P²(M) → H⁰(G_S, M')^∨ → 0` with kernel `Ш²_S(M)` on the left, gives
`#H²(G_S, M) · #H⁰(G_S, M') = #Ш²_S(M) · ∏_{v ∈ S} #H²(K_v, M) · ∏_{w real} #H²(K_w, M)`
(`card_cohomology_two_mul_card_dual_zero`), by the nine-term sequence of Poitou–Tate
(`poitouTateNineTermStatement`).
With local duality at the places of `S`, `#H²(K_v, M) = #H⁰(K_v, M')`
(`card_cohomology_two_localModule_eq`), and when `N` is odd or `K` totally complex (no contribution
of the real places):
`#H²(G_S, M) · #H⁰(G_S, M') = #Ш²_S(M) · ∏_{v ∈ S} #H⁰(K_v, M')`
(`card_cohomology_two_mul_card_dual_zero_eq_prod`).

```lean
theorem card_cohomology_two_mul_card_dual_zero
    (N : ℕ) [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) :
    haveI : Fintype S
theorem card_cohomology_two_localModule_eq (N : ℕ) [NeZero N]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) (v : S) :
    Nat.card (cohomology (localModule ι M v) 2) =
      Nat.card (cohomology (localModule ι (PoitouTate.dual N M) v) 0)
theorem card_cohomology_two_mul_card_dual_zero_eq_prod
    (N : ℕ) [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd N ∨ IsTotallyComplex K)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) :
    haveI : Fintype S
```

## Complete types

In the `#check` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.card_cohomology_two_mul_card_dual_zero : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) →
    ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M],
      (∀ (m : ↑M), N • m = 0) →
        Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 2) *
            Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 0) =
          Nat.card ↥(Langlands.GaloisCohomology.sha ι M 2) *
            ((∏ v,
                Nat.card
                  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 2)) *
              ∏ w,
                Nat.card
                  ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι M ↑w) 2))
@Langlands.GaloisCohomology.card_cohomology_two_localModule_eq : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) →
    ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M],
      (∀ (m : ↑M), N • m = 0) →
        ∀ (v : ↑S),
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.localModule ι M ↑v) 2) =
            Nat.card
              ↑(Langlands.ProfiniteCohomology.cohomology
                  (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑v) 0)
@Langlands.GaloisCohomology.card_cohomology_two_mul_card_dual_zero_eq_prod : ∀ {K Ω : Type u} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [inst_5 : Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) →
    Odd N ∨ NumberField.IsTotallyComplex K →
      ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
        [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M],
        (∀ (m : ↑M), N • m = 0) →
          Nat.card ↑(Langlands.ProfiniteCohomology.cohomology M 2) *
              Nat.card ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dual N M) 0) =
            Nat.card ↥(Langlands.GaloisCohomology.sha ι M 2) *
              ∏ v,
                Nat.card
                  ↑(Langlands.ProfiniteCohomology.cohomology
                      (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dual N M) ↑v) 0)
```

Orders along exact sequences: `card_eq_card_range_mul_card_range` (`#B = #(range f) · #(range g)` at a
place of exactness) and `card_mul_card_eq_of_exact_seven` (`#A₁ · #A₃ · #A₅ · #A₇ = #A₂ · #A₄ · #A₆` along
an exact sequence `0 → A₁ → ⋯ → A₇ → 0`), beside `card_mul_card_eq_of_exact`.

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.card_eq_card_range_mul_card_range.{u_1, u_2, u_3} {A : Type u_1} {B : Type u_2}
  {C : Type u_3} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
  (h : Function.Exact ⇑f ⇑g) : Nat.card B = Nat.card ↥f.range * Nat.card ↥g.range
Langlands.GaloisCohomology.card_mul_card_eq_of_exact_seven.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} {A₁ : Type u_1}
  {A₂ : Type u_2} {A₃ : Type u_3} {A₄ : Type u_4} {A₅ : Type u_5} {A₆ : Type u_6} {A₇ : Type u_7} [AddCommGroup A₁]
  [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅] [AddCommGroup A₆] [AddCommGroup A₇]
  (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅) (f₅ : A₅ →+ A₆) (f₆ : A₆ →+ A₇)
  (h₁ : Function.Injective ⇑f₁) (h₂ : Function.Exact ⇑f₁ ⇑f₂) (h₃ : Function.Exact ⇑f₂ ⇑f₃)
  (h₄ : Function.Exact ⇑f₃ ⇑f₄) (h₅ : Function.Exact ⇑f₄ ⇑f₅) (h₆ : Function.Exact ⇑f₅ ⇑f₆)
  (h₇ : Function.Surjective ⇑f₆) :
  Nat.card A₁ * Nat.card A₃ * Nat.card A₅ * Nat.card A₇ = Nat.card A₂ * Nat.card A₄ * Nat.card A₆
```

## Outline of the proofs

The end of the nine-term sequence `H²(G_S, M) → P²(M) → H⁰(G_S, M')^∨ → 0` is exact with kernel `Ш²` on the left; for an exact sequence `0 → ker f → A → B → C → 0` of finite groups `#A·#C = #ker f·#B`, and `#Hom(X, ℚ/ℤ) = #X`. With local duality at the places of `S` (`bijective_ptLocalPairing_two`) `#H²(K_v, M) = #H⁰(K_v, M')`, and the real `H²` vanish for `N` odd.

- `card_cohomology_two_mul_card_dual_zero`: **The count of `H²` from Poitou–Tate.** For `M` killed by `N`: `#H²(G_S, M) · #H⁰(G_S, M') = #Ш²_S(M) · ∏_{v ∈ S} #H²(K_v, M) · ∏_{w real} #H²(K_w, M)`.
- `card_cohomology_two_localModule_eq`: **Local duality, the count.** At a place `v ∈ S`, `#H²(K_v, M) = #H⁰(K_v, M')` for `M` killed by `N`, `M' = Hom(M, μ_N)`.
- `card_cohomology_two_mul_card_dual_zero_eq_prod`: **The count of `H²` with the local duals.** If `N` is odd or `K` is totally complex, for `M` killed by `N`: `#H²(G_S, M) · #H⁰(G_S, M') = #Ш²_S(M) · ∏_{v ∈ S} #H⁰(K_v, M')`.

## Declarations

`card_mul_card_eq_of_exact`, `exists_prime_dvd_mem_of_natCast_mem`, `mem_of_natCard_mem_of_nsmul_eq_zero`, `finite_cohomology_localModule`, `finite_cohomology_realLocalModule`, `card_cohomology_two_mul_card_dual_zero`, `card_cohomology_two_localModule_eq`, `card_cohomology_two_mul_card_dual_zero_eq_prod`, `card_eq_card_range_mul_card_range`, `card_mul_card_eq_of_exact_seven`.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (BookSurge 2006), I §5, Remark 5.2 (b), formula (5.2.1), p. 67.
- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), (8.6.10), p. 489.
- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. ICM Stockholm 1962, Theorem 2.1, p. 289 (local duality).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShaCount.lean` lines 1–113. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `natCard_cohomology_two_mul_of_poitouTate` → `card_cohomology_two_mul_card_dual_zero`, `natCard_gs_local_cohomology_two` → `card_cohomology_two_localModule_eq`, `natCard_gs_cohomology_two_mul` → `card_cohomology_two_mul_card_dual_zero_eq_prod`.
