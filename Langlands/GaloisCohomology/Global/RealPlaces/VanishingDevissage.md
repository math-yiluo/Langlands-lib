# Dévissage of the vanishing of `Ĥ_cʳ(G_S, M)` to the modules `Coind_W(ℤ/2)`

`Langlands/GaloisCohomology/Global/RealPlaces/VanishingDevissage.lean`, namespace `Langlands.GaloisCohomology`.

**Abstract part.** Let `G` be a compact group with families `(φ_v)` and `(ψ_w)` (the `F_w` finite) and `n`
a degree.

It uses `exists_ne_zero_forall_ρ_eq` (a group acting on a nonzero finite module `N` killed by `2`
through elements of `2`-power order fixes a nonzero vector) and `zmodTwoHom N m` (the morphism
`ℤ/2 → N` sending `1` to a fixed vector `m`) of the module
`Langlands.Cohomology.Profinite.Duality.Devissage`.

* `subsingleton_tateCompactCohomologyRes_coind_of_two_nsmul`: if `Ĥ_cⁿ(G, Coind_W^G(ℤ/2)) = 0`, then
  `Ĥ_cⁿ(G, Coind_W^G N) = 0` for every finite smooth `W`-module `N` killed by `2` on which `W` acts
  through elements of `2`-power order.
* `subsingleton_tateCompactCohomologyRes_of_two_nsmul`: if `Ĥ_cⁿ(G, Coind_W^G(ℤ/2)) = 0` for every open
  subgroup `W`, then `Ĥ_cⁿ(G, M) = 0` for every finite smooth `G`-module `M` killed by `2`.

**For `G_S`** (`r ≥ 4`):

* `subsingleton_compactCohomology_of_odd`: for a prime `ℓ ≠ 2` with the places above `ℓ` in `S` and `M`
  killed by `ℓ`, `Ĥ_cʳ(G_S, M) = 0`;
* `subsingleton_compactCohomology_of_coind`: if `Ĥ_cʳ(G_S, Coind_W(ℤ/2)) = 0` for every open subgroup `W`
  whenever `S` contains the places above `2`, then `Ĥ_cʳ(G_S, M) = 0` for every finite smooth `M` killed by
  an `n ≠ 0` with the places above `n` in `S`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.subsingleton_tateCompactCohomologyRes_coind_of_two_nsmul.{u} {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {κ : Type u}
  {F : κ → Type u} [(w : κ) → Group (F w)] [(w : κ) → TopologicalSpace (F w)] [∀ (w : κ), IsTopologicalGroup (F w)]
  [(w : κ) → Fintype (F w)] (ψ : (w : κ) → F w →ₜ* G) (n : ℕ) (W : OpenSubgroup G)
  (hW :
    Subsingleton
      ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ
          (Rep.coind.{u, u, u, u} (↑W).subtype (Langlands.ProfiniteCohomology.zmodRep (↥↑W) 2)) n))
  (d : ℕ) (N : Rep.{u, u, u} (ULift.{u, 0} ℤ) ↥↑W) [Langlands.IsSmoothRep N] [Finite ↑N] :
  Nat.card ↑N ≤ d →
    (∀ (m : ↑N), 2 • m = 0) →
      (∀ (w : ↥↑W), ∃ k, N.ρ (w ^ 2 ^ k) = 1) →
        Subsingleton
          ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ (Rep.coind.{u, u, u, u} (↑W).subtype N) n)
Langlands.GaloisCohomology.subsingleton_tateCompactCohomologyRes_of_two_nsmul.{u} {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {κ : Type u}
  {F : κ → Type u} [(w : κ) → Group (F w)] [(w : κ) → TopologicalSpace (F w)] [∀ (w : κ), IsTopologicalGroup (F w)]
  [(w : κ) → Fintype (F w)] (ψ : (w : κ) → F w →ₜ* G) (n : ℕ)
  (hW :
    ∀ (W : OpenSubgroup G),
      Subsingleton
        ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ
            (Rep.coind.{u, u, u, u} (↑W).subtype (Langlands.ProfiniteCohomology.zmodRep (↥↑W) 2)) n))
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep M] [Finite ↑M] (h2 : ∀ (m : ↑M), 2 • m = 0) :
  Subsingleton ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ M n)
Langlands.GaloisCohomology.subsingleton_compactCohomology_of_odd.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (h2 : ℓ ≠ 2)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (hM : ∀ (m : ↑M), ℓ • m = 0) {r : ℕ} (hr : 4 ≤ r) :
  Subsingleton ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M r)
Langlands.GaloisCohomology.mem_of_natCast_mem_of_dvd.{u} {K : Type u} [Field K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n d : ℕ} (hd : d ∣ n)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (hv : ↑d ∈ v.asIdeal) : v ∈ S
Langlands.GaloisCohomology.subsingleton_compactCohomology_of_coind.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {r : ℕ} (hr : 4 ≤ r)
  (hC :
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S) →
      ∀ (W : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)),
        Subsingleton
          ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι
              (Rep.coind.{u, u, u, u} (↑W).subtype (Langlands.ProfiniteCohomology.zmodRep (↥↑W) 2)) r))
  (n : ℕ) :
  n ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
      ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
        [inst : Langlands.IsSmoothRep M] [Finite ↑M],
        (∀ (m : ↑M), n • m = 0) → Subsingleton ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M r)
```

## Outline of the proofs

For `M` killed by `2`: let `K₀` be the kernel of the action (open, `M` finite and smooth), `P` a
`2`-Sylow subgroup of `G/K₀` and `W` its preimage; `[G : W]` is odd, so
`coindUnit ≫ coindTrace = [G : W] • 𝟙 = 𝟙` on `M` (`coindUnit_comp_coindTrace`) and `M` is a retract of
`Coind_W Res_W M`. By induction on `#N`: a fixed vector spans `ℤ/2 ⊆ N`
(`cokerShortComplex`), coinduction is exact (`shortExact_coindShortComplexOf`), and the quotient keeps the
hypotheses. For `G_S`: strong induction on `n` through `0 → M[ℓ] → M → M/M[ℓ] → 0`; for `ℓ` odd,
`Hʳ(G_S, M) = 0` for `r ≥ 3` (`cohomologicalDimensionStatement`) and the cohomology of the real places is
killed by `2` and by `ℓ` (`eq_zero_cohomology_closureGalois_of_odd`), and the criterion
`subsingleton_compactCohomology_of_surjective_of_injective` applies.

## Declarations

`subsingleton_tateCompactCohomologyRes_coind_of_two_nsmul`, `subsingleton_tateCompactCohomologyRes_of_two_nsmul`, `subsingleton_compactCohomology_of_odd`, `mem_of_natCast_mem_of_dvd`, `subsingleton_compactCohomology_of_coind`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingIndex.lean` (lines 16–101, 121–260) and `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingPrimes.lean` (lines 86–168). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's `IsSmoothRep`, `fixingOpenSubgroup`, `cokerShortComplex` and `Rep.subrepresentation` replace the source's `IsDiscreteRep`, stabilizer intersection and `subQuotShortComplex`; statements are in `Subsingleton` form; the odd case uses the Library's `cohomologicalDimensionStatement` and `eq_zero_cohomology_closureGalois_of_odd`.

The source's `exists_ne_zero_forall_ρ_eq` and its declarations on `ℤ/2` (`zmodTwoAddHom`, …,
`zmodTwoHom_hom_apply`) are ported in the module `Langlands.Cohomology.Profinite.Duality.Devissage`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter I, §5, Corollary (1.5.7), p. 51 (`cor ∘ res = (G : U)`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6, (8.6.10), pp. 489–491.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57 ((c): `Hʳ(G_S, M) ≅ ∏_{v real} Hʳ(K_v, M)` for `r ≥ 3`); proof pp. 60–61 (p. 61: the exact sequence ending in `H³(G_S, M) → ⊕_{v real} H³(G_v, M) → 0` and the isomorphisms for `r ≥ 4`, from the class formation).
