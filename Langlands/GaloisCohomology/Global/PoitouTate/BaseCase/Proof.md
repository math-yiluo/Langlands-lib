# Poitou–Tate duality for `G_S` from the base case

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Proof.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

With `rootsOfUnityPairingStatement` (`Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Pairing`),
this file gives the hypothesis-free forms of the end theorems of the base case and of the duality at
the finite places.

* `rootsOfUnityDualityStatement : RootsOfUnityDualityStatement` (duality for `μ_n` over the fields
  containing the `n`-th roots of unity);
* `finitePlacesDualityStatement : FinitePlacesDualityStatement` (duality with compact support at
  the finite places, `N` odd or `K` totally complex);
* `bijective_dualityMap_odd`: for `N` odd with the places above `N` in `S` and a finite smooth
  `G_S`-module `M` killed by `N`, `dualityMap ι N M h : Hʳ(G_S, M) → Ĥ_cˢ(G_S, M')^∨` is bijective
  (`r + s = 3`, `s ≥ 1`).

The duality for every `N` and the three statements of Poitou–Tate duality are `bijective_dualityMap`
and `tatePoitouTateHypotheses` of `Reduction.lean` and `poitouTateDualityStatement`,
`poitouTateNineTermStatement`, `poitouTateShaStatement` of `DualityProof.lean`, `NineTermProof.lean`,
`ShaProof.lean` (directory `Global/PoitouTate/`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.rootsOfUnityDualityStatement.{u} :
  Langlands.GaloisCohomology.PoitouTate.RootsOfUnityDualityStatement
Langlands.GaloisCohomology.PoitouTate.finitePlacesDualityStatement.{u} :
  Langlands.GaloisCohomology.PoitouTate.FinitePlacesDualityStatement
Langlands.GaloisCohomology.PoitouTate.bijective_dualityMap_odd.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hN : Odd N) (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hM : ∀ (m : ↑M), N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h)
```

## Outline of the proofs

`rootsOfUnityDualityStatement_of_pairing` and `finitePlacesDualityStatement_of_rootsOfUnity` apply to
`rootsOfUnityPairingStatement`; for `N` odd, `bijective_dualityMap_of_odd` applies to the trace and
the duality at the finite places given by `finitePlacesDualityStatement`.

## Declarations

In the order of the file:

- `rootsOfUnityDualityStatement` (theorem): **The base case of Poitou–Tate duality**: duality for `μ_n` over the fields containing the `n`-th roots of unity.
- `finitePlacesDualityStatement` (theorem): **Duality with compact support at the finite places**, for `N` odd or `K` totally complex.
- `bijective_dualityMap_odd` (theorem): **Poitou–Tate duality for odd `N`.** For `N` odd with the places above `N` in `S` and a finite smooth `G_S`-module `M` killed by `N`, the duality map `Hʳ(G_S, M) → Ĥ_cˢ(G_S, M')^∨` is bijective (`r + s = 3`, `s ≥ 1`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected printing (Springer, 2013), Chapter VIII, §6, Theorem (8.6.7) (Poitou–Tate duality), p. 485; Chapter VIII, §3,
  Theorem (8.3.20), p. 464 (finiteness of the cohomology of `G_S`).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge, 2006), Chapter I, §4, Theorem 4.10, pp. 56–57.
