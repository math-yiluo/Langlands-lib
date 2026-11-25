# The vanishing of `Ĥ_cʳ(G_S, M)` in degrees `≥ 4`: criterion and closure properties

`Langlands/GaloisCohomology/Global/RealPlaces/VanishingCriterion.lean`, namespace `Langlands.GaloisCohomology`.

**Abstract part.** For a group `G` with families `(φ_v : H_v →ₜ* G)` and `(ψ_w : F_w →ₜ* G)` (the `F_w`
finite), the vanishing of the Tate-modified cohomology with compact support
`Ĥ_cⁿ(G, A) = tateCompactCohomologyRes φ ψ A n` in a fixed degree `n` passes to extensions
(`subsingleton_tateCompactCohomologyRes_of_shortExact`: if `0 → A₁ → A₂ → A₃ → 0` is exact and
`Ĥ_cⁿ(A₁) = Ĥ_cⁿ(A₃) = 0`, then `Ĥ_cⁿ(A₂) = 0`) and to retracts
(`subsingleton_tateCompactCohomologyRes_of_retract`), both of the module
`Langlands.GaloisCohomology.CompactSupport.TateModified.Duality`; it holds for the zero module
(`PoitouTate.subsingleton_tateCompactCohomologyRes` of the module
`Langlands.GaloisCohomology.Global.PoitouTate.Assembly`).

**For `G_S`.** Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places,
`ι : PlaceEmbeddings K Ω`, `Ĥ_cʳ(G_S, M) = compactCohomology ι M r`, and `M` a smooth `G_S`-module killed by
`n ≠ 0`. At the finite places the local groups have no cohomology in degrees `≥ 3`, so for `r ≥ 3` the
exact sequence `Ĥ_cʳ(G_S, M) → Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M) → Ĥ_cʳ⁺¹(G_S, M) → Hʳ⁺¹(G_S, M)` gives:

* `subsingleton_compactCohomology_of_surjective_of_injective`: if the localization to the real places is
  surjective in degree `r` and injective in degree `r + 1`, then `Ĥ_cʳ⁺¹(G_S, M) = 0`;
* `injective_realLocalization_of_subsingleton`: if `Ĥ_cʳ(G_S, M) = 0`, the localization to the real places
  is injective in degree `r`;
* `surjective_realLocalization_of_subsingleton`: if `Ĥ_cʳ⁺¹(G_S, M) = 0`, it is surjective in degree `r`
  (this one needs neither `n` nor `r ≥ 3`, only `r ≥ 1` through the form of the statement).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.subsingleton_compactCohomology_of_surjective_of_injective.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} (hn : n ≠ 0)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (hM : ∀ (m : ↑M), n • m = 0) {r : ℕ} (hr : 3 ≤ r)
  (hs : Function.Surjective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x)
  (hi : Function.Injective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) (r + 1)) x) :
  Subsingleton ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M (r + 1))
Langlands.GaloisCohomology.injective_realLocalization_of_subsingleton.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ} (hn : n ≠ 0)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (hM : ∀ (m : ↑M), n • m = 0) {r : ℕ} (hr : 3 ≤ r)
  (h : Subsingleton ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M r)) :
  Function.Injective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
Langlands.GaloisCohomology.surjective_realLocalization_of_subsingleton.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  {r : ℕ} (hr : 3 ≤ r) (h : Subsingleton ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M (r + 1))) :
  Function.Surjective fun x w => (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
```

## Outline of the proofs

Extensions: exactness of `Ĥ_cⁿ(A₁) → Ĥ_cⁿ(A₂) → Ĥ_cⁿ(A₃)` (`tateCompactRes_exact₂`). Retracts: functoriality
(`tateCompactCohomologyResMap_comp`, `tateCompactCohomologyResMap_id`). The criterion:
exactness of the Tate-modified sequence at `Ĥ_cʳ⁺¹`, `Hʳ⁺¹` and at the local terms (`ptTExact_compact`,
`ptTExact_global`, `ptTExact_local`), the finite local terms vanishing by
`subsingleton_cohomology_localModule_of_three_le`.

## Declarations

`subsingleton_compactCohomology_of_surjective_of_injective`, `injective_realLocalization_of_subsingleton`, `surjective_realLocalization_of_subsingleton`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingCriterion.lean` (lines 26–80 and 82–155: `tateCompactCohomology_eq_zero_of_surjective_of_injective`, `injective_tateGlobalToLocal_of_eq_zero`, `surjective_tateGlobalToLocal_of_eq_zero`, `eq_zero_tateCompactCohomologyRes_of_shortExact`, `eq_zero_tateCompactCohomologyRes_of_retract`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The statements are in `Subsingleton` form; the criterion is stated for `G_S` with the Library's `compactCohomology` and `realLocalization`, the finite local terms being disposed of inside the proofs (the source's `injective_tateGlobalToLocal_iff` and `surjective_tateGlobalToLocal_iff`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6, (8.6.10) (long exact sequence of Poitou–Tate; (ii): `Hⁱ(G_S, A) ≅ ⊕_{𝔭 real} Hⁱ(k_𝔭, A)` for `i ≥ 3`), statement p. 489, proof of (ii) pp. 490–491 (degree `3` from the duality of the class formation (8.4.4) and (7.2.17); the degrees `i ≥ 3` by the exact sequence `0 → A → Ind A → B → 0` and induction).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57 ((c): `Hʳ(G_S, M) ≅ ∏_{v real} Hʳ(K_v, M)` for `r ≥ 3`); proof pp. 60–61 (p. 61: the exact sequence ending in `H³(G_S, M) → ⊕_{v real} H³(G_v, M) → 0` and the isomorphisms for `r ≥ 4`, from the class formation).
