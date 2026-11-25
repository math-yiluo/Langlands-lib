# Duality with compact support at the finite places

`Langlands/GaloisCohomology/Global/PoitouTate/FinitePlaces.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

When `N` is odd or `K` has no real place, the real places play no role in Poitou–Tate duality for
modules killed by `N`, and the duality can be stated with the cohomology with compact support
`H_c^•(G_S, ·)` taken with respect to the places of `S` only (`compactSupportCohomologyRes` of the
family `localFamily ι S`).

`FinitePlacesDualityStatement` says: for every such `K`, `S`, `N`, there is a trace
`T : H_c³(G_S, μ_N) → ℤ/N` that restricts on `∏_{v ∈ S} H²(K_v, μ_N)` to the sum of the local
invariants, and for which the duality map `Hʳ(G_S, M) → Hom(H_cˢ(G_S, M'), ℤ/N)` (cup product with the
evaluation followed by `T`) is bijective for every finite module `M` killed by `N` and every
`r + s = 3`. It is the form in which the base case of the duality and the reduction to prime powers
enter the proof of `PoitouTateDualityStatement`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.FinitePlacesDualityStatement.{u} : Prop
Langlands.GaloisCohomology.PoitouTate.IsFiniteTrace.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ)
  (T :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
      ZMod N) :
  Prop
Langlands.GaloisCohomology.PoitouTate.forgetReal.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep A]
  (n : ℕ) :
  Langlands.GaloisCohomology.PoitouTate.compactCohomology ι A n ⟶
    Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S) A n
```

## Outline of the proofs

Definitions and the statement only.

## Declarations

`IsFiniteTrace`, `forgetReal`, `FinitePlacesDualityStatement`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
