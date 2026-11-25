# Poitou–Tate duality for `G_S`: statement

`Langlands/GaloisCohomology/Global/PoitouTate/DualityStatement.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure of `K`, `S` a finite set of finite places of `K`
containing the places above `N ≥ 1`, `G_S = Gal(K_S/K)`, and `M` a finite smooth `G_S`-module killed
by `N`, with dual `M' = Hom(M, μ_N)`. Let `Ĥ_c^•(G_S, ·)` be the cohomology with compact support with
respect to the places of `S` and the real places, in which degree `0` at the real places is Tate's
`Ĥ⁰` (`PoitouTate.compactCohomology`). Poitou–Tate duality says that the cup product with the
evaluation `M ⊗ M' → μ_N` followed by the trace `Ĥ_c³(G_S, μ_N) → ℤ/N` gives perfect pairings

* `Hʳ(G_S, M) × Ĥ_cˢ(G_S, M') → ℤ/N` for `r + s = 3`, `s ≥ 1` (`PoitouTate.dualityMap`), and
* `Ĥ_cʳ(G_S, M) × Hˢ(G_S, M') → ℚ/ℤ` for `r + s = 3`, `r ≥ 1` (`PoitouTate.compactDualityMap`).

`PoitouTate.IsDuality ι N M` is the conjunction of the two bijectivities and
`PoitouTateDualityStatement` asserts it for all `K`, `Ω`, `S`, `ι`, `N` and `M`, with no condition on
the parity of `N` or on the real places. It is proved in
`Langlands.GaloisCohomology.Global.PoitouTate.DualityProof`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.IsDuality.bijective_compactDualityMap.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M) {r s : ℕ} (h : r + s = 3) :
  1 ≤ r → Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.compactDualityMap ι N M h)
Langlands.GaloisCohomology.PoitouTate.IsDuality.bijective_dualityMap.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] (self : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M) {r s : ℕ} (h : r + s = 3) :
  1 ≤ s → Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h)
Langlands.GaloisCohomology.PoitouTate.IsDuality.mk.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M]
  (bijective_dualityMap :
    ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s → Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h))
  (bijective_compactDualityMap :
    ∀ {r s : ℕ} (h : r + s = 3),
      1 ≤ r → Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.compactDualityMap ι N M h)) :
  Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M
Langlands.GaloisCohomology.PoitouTate.IsDuality.rec.{u_1, u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] {ι : Langlands.Galois.PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)} [Langlands.IsSmoothRep M]
  [Finite ↑M] {motive : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M → Sort u_1}
  (mk :
    (bijective_dualityMap :
        ∀ {r s : ℕ} (h : r + s = 3),
          1 ≤ s → Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h)) →
      (bijective_compactDualityMap :
          ∀ {r s : ℕ} (h : r + s = 3),
            1 ≤ r → Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.compactDualityMap ι N M h)) →
        motive ⋯)
  (t : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M) : motive t
Langlands.GaloisCohomology.PoitouTate.IsDuality.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] : Prop
Langlands.GaloisCohomology.PoitouTateDualityStatement.{u} : Prop
```

## Outline of the proofs

Statement only.

## Declarations

`IsDuality`, `PoitouTateDualityStatement`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
