# The trace for the cohomology with compact support at the finite places

`Langlands/GaloisCohomology/Global/PoitouTate/FiniteTrace.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

When `N` is odd or `K` is totally complex, the real places contribute nothing to the sum formula for
classes of `H²(G_S, μ_N)`: the sum over `v ∈ S` of the local invariants of the localizations vanishes
(`sum_invariantAt_localization`). Hence the sum of the local invariants on
`∏_{v ∈ S} H²(K_v, μ_N)` factors through `H_c³(G_S, μ_N)` (cohomology with compact support at the
places of `S`), which gives the trace `finiteTrace : H_c³(G_S, μ_N) → ℤ/N` with
`IsFiniteTrace` (`isFiniteTrace_finiteTrace`). When moreover `S` contains the places above `N`, the
map `∏_{v ∈ S} H²(K_v, μ_N) → H_c³(G_S, μ_N)` is onto (`H³(G_S, μ_N) = 0`), and a trace with
`IsFiniteTrace` is unique (`eq_finiteTrace_of_isFiniteTrace`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.eq_finiteTrace_of_isFiniteTrace.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (T :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
      ZMod N)
  (hT : Langlands.GaloisCohomology.PoitouTate.IsFiniteTrace ι S N T) :
  T = Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S N hK
Langlands.GaloisCohomology.PoitouTate.finiteSumInvariants.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) :
  ((v : ↑S) →
      ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) ↑v)
          2)) →+
    Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.finiteSumInvariants_apply.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ)
  (ξ :
    (v : ↑S) →
      ↑(Langlands.ProfiniteCohomology.cohomology
          (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) ↑v)
          2)) :
  (Langlands.GaloisCohomology.PoitouTate.finiteSumInvariants ι S N) ξ =
    ∑ v, (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) (ξ v)
Langlands.GaloisCohomology.PoitouTate.finiteTrace.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K) :
  ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
    ZMod N
Langlands.GaloisCohomology.PoitouTate.finiteTraceQZ.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K) :
  ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3) →+
    Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.PoitouTate.finiteTraceQZ_comp.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K) :
  (Langlands.GaloisCohomology.PoitouTate.finiteTraceQZ ι S N hK).comp
      (ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.ptLocalToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)).toAddMonoidHom =
    Langlands.GaloisCohomology.PoitouTate.finiteSumInvariants ι S N
Langlands.GaloisCohomology.PoitouTate.isFiniteTrace_finiteTrace.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K) :
  Langlands.GaloisCohomology.PoitouTate.IsFiniteTrace ι S N (Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S N hK)
Langlands.GaloisCohomology.PoitouTate.ker_ptLocalToCompact_le_ker_finiteSumInvariants.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K) :
  (ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.ptLocalToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
            (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)).toAddMonoidHom.ker ≤
    (Langlands.GaloisCohomology.PoitouTate.finiteSumInvariants ι S N).ker
Langlands.GaloisCohomology.PoitouTate.nsmul_finiteTraceQZ.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K)
  (z :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 3)) :
  N • (Langlands.GaloisCohomology.PoitouTate.finiteTraceQZ ι S N hK) z = 0
Langlands.GaloisCohomology.PoitouTate.sum_invariantAt_localization.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K) [Fintype ↑S]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2)) :
  ∑ v,
      (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v)
        ((Langlands.GaloisCohomology.localization ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) (↑v)
            2)
          x) =
    0
Langlands.GaloisCohomology.PoitouTate.surjective_ptLocalToCompact_two.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) :
  Function.Surjective
    ⇑(ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.ptLocalToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) 2))
```

## Outline of the proofs

As `Trace.lean` without the real places: the real invariants of classes of `H²(G_S, μ_N)` vanish when `N` is odd (`eq_zero_cohomology_closureGalois_of_odd`) or there are no real places.

## Declarations

`sum_invariantAt_localization`, `finiteSumInvariants`, `finiteSumInvariants_apply`, `ker_ptLocalToCompact_le_ker_finiteSumInvariants`, `finiteTraceQZ`, `finiteTraceQZ_comp`, `nsmul_finiteTraceQZ`, `finiteTrace`, `isFiniteTrace_finiteTrace`, `surjective_ptLocalToCompact_two`, `eq_finiteTrace_of_isFiniteTrace`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
