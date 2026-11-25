# The duality at the finite places from the fields containing the roots of unity

`Langlands/GaloisCohomology/Global/PoitouTate/FinitePlacesProof.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

`RootsOfUnityDualityStatement` is the duality for `ℤ/n` with compact support at the places of `S`
(`compactZmodDualityMap`, with the trace `finiteTrace`) for the number fields containing the `n`-th
roots of unity, `n` a prime power with the places above `n` in `S`, `n` odd or the field totally
complex. This file proves `FinitePlacesDualityStatement` from it
(`finitePlacesDualityStatement_of_rootsOfUnity`):

* for `N = q` a prime power, by the dévissage `CompactDualityHypotheses` of the abstract layer: the
  cohomology with compact support vanishes in degree `4` (`subsingleton_compactSupportCohomologyRes_of_four_le`,
  from `cd ≤ 2` globally and locally), and for an open subgroup `U` fixing `K(μ_q)` the duality for
  `ℤ/q` over `U` is that of its fixed field `L ⊇ μ_q`
  (`bijective_zmodCompactDualityMap_of_rootsOfUnity`, through `bijective_compactZmodDualityMap_fixingOpenSubgroup`);
* for general `N`, by the reduction to prime powers `bijective_compactDualityMap_of_primePow`, the
  traces of the primary parts being compatible through the local invariants
  (`zmodToQZ_finiteTrace_rootsOfUnityInclusion`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.RootsOfUnityDualityStatement.{u} : Prop
Langlands.GaloisCohomology.PoitouTate.bijective_compactDualityMap_of_rootsOfUnity.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (q : ℕ) [NeZero q]
  (hbase : Langlands.GaloisCohomology.PoitouTate.RootsOfUnityDualityStatement) (hq : IsPrimePow q)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑q ∈ v.asIdeal → v ∈ S)
  (hK : Odd q ∨ NumberField.IsTotallyComplex K)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hM : ∀ (m : ↑M), q • m = 0) {r s : ℕ} (h : r + s = 3) :
  Function.Bijective
    ⇑(Langlands.GaloisCohomology.compactDualityMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S q) h
        (Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S q hK) M)
Langlands.GaloisCohomology.PoitouTate.bijective_zmodCompactDualityMap_of_rootsOfUnity.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (q : ℕ) [NeZero q]
  (hbase : Langlands.GaloisCohomology.PoitouTate.RootsOfUnityDualityStatement) (hq : IsPrimePow q)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑q ∈ v.asIdeal → v ∈ S)
  (hK : Odd q ∨ NumberField.IsTotallyComplex K)
  (hV :
    ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst : Langlands.IsSmoothRep M] [Finite ↑M],
      (∀ (m : ↑M), q • m = 0) →
        Subsingleton
          ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes
              (Langlands.GaloisCohomology.PoitouTate.localFamily ι S) M 4))
  {ζ : Ω} (hζ : IsPrimitiveRoot ζ q) (hζS : ζ ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  {L₀ : IntermediateField K Ω} [NumberField ↥L₀]
  (hL₀ : ∀ (x : ↥L₀), (algebraMap (↥L₀) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (hL₀ζ : L₀ = K⟮ζ⟯)
  (hD : ∀ (d : ↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S q)), q • d = 0)
  (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) {L : IntermediateField K Ω} [NumberField ↥L]
  (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (hUL : Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL = U)
  (hU : U ≤ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) {r s : ℕ} (h : r + s = 3) :
  Function.Bijective
    ⇑(Langlands.GaloisCohomology.zmodCompactDualityMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S q) hD U h
        (Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S q hK))
Langlands.GaloisCohomology.PoitouTate.exists_compactDualityHypotheses_of_rootsOfUnity.match_1_1.{u_1} {K Ω : Type u_1}
  [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) (L : IntermediateField K Ω)
  (motive :
    (∃ (x : NumberField ↥L) (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
        Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL = U) →
      Prop)
  (x✝ :
    ∃ (x : NumberField ↥L) (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
      Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL = U)
  (h_1 :
    ∀ (w : NumberField ↥L) (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
      (hUL : Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL = U), motive ⋯) :
  motive x✝
Langlands.GaloisCohomology.PoitouTate.exists_compactDualityHypotheses_of_rootsOfUnity.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (q : ℕ) [NeZero q]
  (hbase : Langlands.GaloisCohomology.PoitouTate.RootsOfUnityDualityStatement) (hq : IsPrimePow q)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑q ∈ v.asIdeal → v ∈ S)
  (hK : Odd q ∨ NumberField.IsTotallyComplex K) :
  ∃ U₀,
    Langlands.GaloisCohomology.CompactDualityHypotheses (Langlands.GaloisCohomology.PoitouTate.localFamily ι S) q
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S q)
      (Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S q hK) U₀
Langlands.GaloisCohomology.PoitouTate.finitePlacesDualityStatement_of_rootsOfUnity.{u}
  (hbase : Langlands.GaloisCohomology.PoitouTate.RootsOfUnityDualityStatement) :
  Langlands.GaloisCohomology.PoitouTate.FinitePlacesDualityStatement
Langlands.GaloisCohomology.PoitouTate.injective_rootsOfUnityInclusion.{u} {K Ω : Type u} [Field K] [Field Ω]
  [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {d N : ℕ} (hd : d ∣ N) :
  Function.Injective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityInclusion S hd))
Langlands.GaloisCohomology.PoitouTate.invariantAt_coeffMap_rootsOfUnityInclusion.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {d N : ℕ} (hd : d ∣ N) (v : ↑S)
  (ξ :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.localModule ι (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S d) ↑v)
        2)) :
  (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v)
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap
            (Langlands.GaloisCohomology.resMorphism (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityInclusion S hd) v)
            2))
        ξ) =
    (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S d ↑v) ξ
Langlands.GaloisCohomology.PoitouTate.mem_range_of_pow_eq_one.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (q : ℕ)
  [NeZero q] {ζ : Ω} (hζ : IsPrimitiveRoot ζ q) (hζS : ζ ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  {L₀ : IntermediateField K Ω} [NumberField ↥L₀]
  (hL₀ : ∀ (x : ↥L₀), (algebraMap (↥L₀) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (hL₀ζ : L₀ = K⟮ζ⟯)
  {L : IntermediateField K Ω} [NumberField ↥L]
  (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (hU :
    Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL ≤
      Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀)
  (z : Ω) : z ^ q = 1 → z ∈ (algebraMap (↥L) Ω).range
Langlands.GaloisCohomology.PoitouTate.rootsOfUnityInclusion.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {d N : ℕ} (hd : d ∣ N) :
  Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S d ⟶
    Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N
Langlands.GaloisCohomology.PoitouTate.subsingleton_compactSupportCohomologyRes_of_four_le.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ NumberField.IsTotallyComplex K)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  (hM : ∀ (m : ↑M), n • m = 0) {r : ℕ} (hr : 4 ≤ r) :
  Subsingleton
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S) M
        r)
Langlands.GaloisCohomology.PoitouTate.surjective_finiteTrace.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hK : Odd N ∨ NumberField.IsTotallyComplex K) (hN : N ≠ 1)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) :
  Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S N hK)
Langlands.GaloisCohomology.PoitouTate.zmodToQZ_finiteTrace_rootsOfUnityInclusion.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] {d N : ℕ} [NeZero d]
  [NeZero N] (hd : d ∣ N) (hKd : Odd d ∨ NumberField.IsTotallyComplex K) (hKN : Odd N ∨ NumberField.IsTotallyComplex K)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑d ∈ v.asIdeal → v ∈ S)
  (z :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S d) 3)) :
  (Langlands.ProfiniteCohomology.zmodToQZ N)
      ((Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S N hKN)
        ((ModuleCat.Hom.hom
            (Langlands.GaloisCohomology.compactSupportCohomologyResMap
              (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
              (Langlands.GaloisCohomology.PoitouTate.rootsOfUnityInclusion S hd) 3))
          z)) =
    (Langlands.ProfiniteCohomology.zmodToQZ d) ((Langlands.GaloisCohomology.PoitouTate.finiteTrace ι S d hKd) z)
```

## Outline of the proofs

Prime powers: `CompactDualityHypotheses` with `U₀` the subgroup fixing `K(ζ_q)`; for `U ≤ U₀` with fixed field `L ⊇ μ_q` (`mem_range_of_pow_eq_one`, by the Galois correspondence `InfiniteGalois.fixedField_fixingSubgroup`) the duality over `U` is transported from `L` (`bijective_compactZmodDualityMap_fixingOpenSubgroup`); `H_c⁴ = 0` from `cd ≤ 2`. Composite `N`: `bijective_compactDualityMap_of_primePow`, the traces being compatible through the invariants (`invariantAt_coeffMap_rootsOfUnityInclusion`) and the naturality of `∏ H² → H_c³` (`compactSupportCohomologyResMap_ptLocalToCompact`).

## Declarations

`RootsOfUnityDualityStatement`, `subsingleton_compactSupportCohomologyRes_of_four_le`, `surjective_finiteTrace`, `mem_range_of_pow_eq_one`, `bijective_zmodCompactDualityMap_of_rootsOfUnity`, `exists_compactDualityHypotheses_of_rootsOfUnity`, `bijective_compactDualityMap_of_rootsOfUnity`, `rootsOfUnityInclusion`, `injective_rootsOfUnityInclusion`, `invariantAt_coeffMap_rootsOfUnityInclusion`, `zmodToQZ_finiteTrace_rootsOfUnityInclusion`, `finitePlacesDualityStatement_of_rootsOfUnity`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
