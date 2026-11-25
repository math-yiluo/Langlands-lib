# Poitou–Tate duality for odd `N`

`Langlands/GaloisCohomology/Global/PoitouTate/OddDuality.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

For `N` odd, the real places contribute nothing to the cohomology of modules killed by `N` in
positive degrees: `Gal(ℂ/ℝ)` has order two, so `Hⁿ(K_w, A) = 0` for `n ≥ 1`, and every invariant of
`A` is a norm. Hence forgetting the real places is an isomorphism `Ĥ_cⁿ(G_S, A) ≅ H_cⁿ(G_S, A)` for
`n ≥ 1` (`bijective_tateForget_of_odd`, from `isIso_tateForget`), the trace `trace` is a trace for
the compact support at the finite places composed with this isomorphism (`trace_eq_comp_tateForget`),
and the duality map with the real places is the duality map without them composed with it
(`dualityMap_eq_of_odd`). So Poitou–Tate duality with the real places follows from the duality at
the finite places (`bijective_dualityMap_of_odd`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.bijective_dualityMap_of_odd.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hN : Odd N) (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (T :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
      ZMod N)
  (hT : Langlands.GaloisCohomology.PoitouTate.IsFiniteTrace ι S N T)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M]
  (hdual :
    ∀ {r s : ℕ} (h : r + s = 3),
      Function.Bijective
        ⇑(Langlands.GaloisCohomology.compactDualityMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) h T M))
  {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h)
Langlands.GaloisCohomology.PoitouTate.bijective_tateForget_of_odd.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {N : ℕ} (hN : Odd N)
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep A]
  (hA : ∀ (a : ↑A), N • a = 0) {n : ℕ} (hn : 1 ≤ n) :
  Function.Bijective ⇑(ModuleCat.Hom.hom (Langlands.GaloisCohomology.PoitouTate.forgetReal ι S A n))
Langlands.GaloisCohomology.PoitouTate.dualityMap_eq_of_odd.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hN : Odd N) (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (T :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
      ZMod N)
  (hT : Langlands.GaloisCohomology.PoitouTate.IsFiniteTrace ι S N T)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] {r s : ℕ} (h : r + s = 3) (x : ↑(Langlands.ProfiniteCohomology.cohomology M r))
  (y :
    ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι (Langlands.GaloisCohomology.PoitouTate.dual N M) s)) :
  ((Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h) x) y =
    ((Langlands.GaloisCohomology.compactDualityMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) h T M)
        x)
      ((ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.PoitouTate.forgetReal ι S (Langlands.GaloisCohomology.PoitouTate.dual N M) s))
        y)
Langlands.GaloisCohomology.PoitouTate.exists_norm_realLocalModule_of_odd.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {N : ℕ} (hN : Odd N)
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  (hA : ∀ (a : ↑A), N • a = 0) (w : { w // w.IsReal }) (x : ↑(Langlands.GaloisCohomology.realLocalModule ι A ↑w)) :
  x ∈ (Langlands.GaloisCohomology.realLocalModule ι A ↑w).ρ.invariants →
    ∃ m, (Langlands.GaloisCohomology.realLocalModule ι A ↑w).ρ.norm m = x
Langlands.GaloisCohomology.PoitouTate.isZero_cohomology_realLocalModule_of_odd.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {N : ℕ} (hN : Odd N)
  (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep A]
  (hA : ∀ (a : ↑A), N • a = 0) (w : { w // w.IsReal }) (n : ℕ) :
  CategoryTheory.Limits.IsZero
    (Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.realLocalModule ι A ↑w) (n + 1))
Langlands.GaloisCohomology.PoitouTate.surjective_ptTLocalToCompact_two_of_odd.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N] (hN : Odd N)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) :
  Function.Surjective
    ⇑(ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.ptTLocalToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2))
Langlands.GaloisCohomology.PoitouTate.trace_eq_comp_tateForget.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hN : Odd N) (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (T :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
      ZMod N)
  (hT : Langlands.GaloisCohomology.PoitouTate.IsFiniteTrace ι S N T) :
  Langlands.GaloisCohomology.PoitouTate.trace ι S N =
    T.comp
      (ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.PoitouTate.forgetReal ι S
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3)).toAddMonoidHom
```

## Outline of the proofs

For `N` odd, `Gal(ℂ/ℝ)` has no cohomology in positive degrees with coefficients killed by `N` and every invariant is a norm; `isIso_tateForget` then identifies the two cohomologies with compact support, and `H³(G_S, μ_N) = 0` (`cohomologicalDimensionStatement`) shows that the trace is the trace at the finite places after forgetting the real places.

## Declarations

`isZero_cohomology_realLocalModule_of_odd`, `exists_norm_realLocalModule_of_odd`, `bijective_tateForget_of_odd`, `surjective_ptTLocalToCompact_two_of_odd`, `trace_eq_comp_tateForget`, `dualityMap_eq_of_odd`, `bijective_dualityMap_of_odd`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
