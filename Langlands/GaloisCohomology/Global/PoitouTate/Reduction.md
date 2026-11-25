# Poitou–Tate for `G_S`: the duality with the real places and the abstract hypotheses

`Langlands/GaloisCohomology/Global/PoitouTate/Reduction.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

This file proves, for every `N`, Poitou–Tate duality for `G_S` with the real places,
`bijective_dualityMap` (for a finite smooth `G_S`-module `M` killed by `N`, with the places above `N`
in `S`, the duality map `Hʳ(G_S, M) → Ĥ_cˢ(G_S, M')^∨` is bijective, `r + s = 3`, `s ≥ 1`), and the
abstract hypotheses of the Tate-modified nine-term sequence (`TatePoitouTateHypotheses`) for `G_S`,
`tatePoitouTateHypotheses` (`N ≠ 1`), from

* local Tate duality at the finite places (`localTateDualityStatement`),
* the duality without real places, `finitePlacesDualityStatement` of `BaseCase/Proof.lean` (for `N`
  odd it gives the duality directly, `bijective_dualityMap_of_odd`; for `N` even it is used for the
  totally complex fields `L ⊆ K_S`, `bijective_dualityMap_of_even`),
* the vanishing of the Tate-modified cohomology with compact support in degrees `≥ 4`,
  `tateCompactSupportVanishingStatement` of
  `Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof`, of which `N` even needs
  `Ĥ_c⁴(G_S, M) = 0`.

The three statements of Poitou–Tate duality follow from `tatePoitouTateHypotheses`
(`poitouTateDualityStatement`, `poitouTateNineTermStatement`, `poitouTateShaStatement` of
`DualityProof.lean`, `NineTermProof.lean`, `ShaProof.lean` in this directory).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.bijective_dualityMap.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hM : ∀ (m : ↑M), N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h)
Langlands.GaloisCohomology.PoitouTate.tatePoitouTateHypotheses.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (hN : N ≠ 1) :
  Langlands.GaloisCohomology.TatePoitouTateHypotheses (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
    (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
    (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) (Langlands.GaloisCohomology.PoitouTate.trace ι S N)
    (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) fun w =>
    Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w
```

## Outline of the proofs

`N` odd: `bijective_dualityMap_of_odd` with `finitePlacesDualityStatement`; `N` even: `bijective_dualityMap_of_even` with `finitePlacesDualityStatement` and `tateCompactSupportVanishingStatement` in degree `4`; then `tatePoitouTateHypotheses_of` (local Tate duality enters there, through `surjective_localPairing`) with `bijective_dualityMap`.

## Declarations

`bijective_dualityMap`, `tatePoitouTateHypotheses`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
