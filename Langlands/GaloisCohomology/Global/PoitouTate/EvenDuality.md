# Poitou–Tate duality for even `N`

`Langlands/GaloisCohomology/Global/PoitouTate/EvenDuality.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

For `N` even the real places matter, and the duality with the Tate-modified cohomology with
compact support is obtained from the abstract dévissage `TateCompactDualityHypotheses`: the
vanishing of `Ĥ_c⁴(G_S, M)` for finite modules killed by `N`, and the duality for the modules
coinduced from `ℤ/N` on open subgroups `U` of `G_S` fixing `K(i)`. Such a `U` meets the conjugates of
the complex conjugations trivially (`freeOnCosets_of_le`), so `Ĥ_c(G_S, Coind_U ℤ/N)` is `H_c(U, ℤ/N)`
for the Mackey family, and `U` is `G_{S_L}(L)` for its fixed field `L`, which is totally complex
(`isTotallyComplex_of_le`). The duality for `ℤ/N` over `U` is then the duality without real places
for `L` (`FinitePlacesDualityStatement`), transported by `bijective_compactZmodDualityMap_fixingOpenSubgroup`;
the traces differ by a unit because the trace of `G_S` is surjective (`surjective_trace`, from the
local Kummer sequences, `exists_invariantAt_eq`) and corestriction to `Ĥ_c³` is surjective.

## Main results

* `exists_invariantAt_eq`: every element of `(1/N)ℤ/ℤ` is a local invariant of `H²(K_v, μ_N)`.
* `surjective_trace`: the trace `Ĥ_c³(G_S, μ_N) → ℤ/N` is surjective for `N ≠ 1`.
* `exists_eq_mul_of_bijective_zero`: with `compactCupRes_zmodH0Class_of_surjective` of the module
  `Langlands.GaloisCohomology.CompactSupport.BaseCase` (cup product with the class of `a ∈ ℤ/N` in degree
  `0` is multiplication by `a` on `H_c³`, when `∏ H²(local) → H_c³` is onto), every map `H_c³ → ℤ/N` is a
  multiple of the trace when the duality for `ℤ/N` holds in degrees `(0, 3)`.
* `bijective_dualityMap_of_even`: Poitou–Tate duality for `N` even from the vanishing of `Ĥ_c⁴` and
  the duality without real places for the totally complex fields `L ⊆ K_S`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.apply_sqrt_neg_one_of_mem.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {i : Ω}
  (hiS : i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) {L₀ : IntermediateField K Ω} [NumberField ↥L₀]
  (hL₀ : ∀ (x : ↥L₀), (algebraMap (↥L₀) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (hL₀i : L₀ = K⟮i⟯)
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
  (hσ : σ ∈ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) : σ ⟨i, hiS⟩ = ⟨i, hiS⟩
Langlands.GaloisCohomology.PoitouTate.bijective_dualityMap_of_even.match_1_1.{u_1} {K Ω : Type u_1} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
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
Langlands.GaloisCohomology.PoitouTate.bijective_dualityMap_of_even.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hfin : Langlands.GaloisCohomology.PoitouTate.FinitePlacesDualityStatement) (hN : Even N)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (hV :
    ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst : Langlands.IsSmoothRep M] [Finite ↑M],
      (∀ (m : ↑M), N • m = 0) → Subsingleton ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M 4))
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] (hM : ∀ (m : ↑M), N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.PoitouTate.dualityMap ι N M h)
Langlands.GaloisCohomology.PoitouTate.bijective_tateCompactDualityMap_coind_fixingOpenSubgroup.{u} {K Ω : Type u}
  [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] (N : ℕ) [NeZero N]
  (hfin : Langlands.GaloisCohomology.PoitouTate.FinitePlacesDualityStatement) (hN : N ≠ 1)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (hV :
    ∀ (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst : Langlands.IsSmoothRep M] [Finite ↑M],
      (∀ (m : ↑M), N • m = 0) → Subsingleton ↑(Langlands.GaloisCohomology.PoitouTate.compactCohomology ι M 4))
  {i : Ω} (hi : i ^ 2 = -1) (hiS : i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) {L₀ : IntermediateField K Ω}
  [NumberField ↥L₀] (hL₀ : ∀ (x : ↥L₀), (algebraMap (↥L₀) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (hL₀i : L₀ = K⟮i⟯) (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  {L : IntermediateField K Ω} [NumberField ↥L]
  (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (hUL : Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL = U)
  (hU : U ≤ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) {r s : ℕ} (h : r + s = 3)
  (hs : 1 ≤ s) :
  Function.Bijective
    ⇑(Langlands.GaloisCohomology.tateCompactDualityMap (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
        (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N) h
        (Langlands.GaloisCohomology.PoitouTate.trace ι S N)
        (Rep.coind.{u, u, u, u} (↑U).subtype (Langlands.ProfiniteCohomology.zmodRep (↥↑U) N)))
Langlands.GaloisCohomology.PoitouTate.conj_realLocalizationHom_closureConj_apply.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {i : Ω} (hi : i ^ 2 = -1)
  (hiS : i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (x : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)
  (w : NumberField.InfinitePlace K) (hw : w.IsReal) :
  (x * (Langlands.Galois.realLocalizationHom ι S w) (Langlands.GaloisCohomology.closureConj w hw) * x⁻¹) ⟨i, hiS⟩ =
    -⟨i, hiS⟩
Langlands.GaloisCohomology.PoitouTate.exists_eq_mul_of_bijective_zero.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)]
  [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {n : ℕ} [NeZero n]
  (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D] (hD : ∀ (d : ↑D), n • d = 0) (h : 0 + 3 = 3)
  (hsurj :
    Function.Surjective
      ⇑(ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.localToCompact φ D (fun v => Rep.res (↑(φ v)) D)
            (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) D)) 2)))
  (T : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ D 3) →+ ZMod n)
  (hb : Function.Bijective ⇑(Langlands.GaloisCohomology.compactZmodDualityMap φ D hD T h))
  (χ : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ D 3) →+ ZMod n) :
  ∃ c, ∀ (y : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ D 3)), χ y = c * T y
Langlands.GaloisCohomology.PoitouTate.exists_invariantAt_eq.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (q : Langlands.ProfiniteCohomology.QZ)
  (hq : N • q = 0) : ∃ ξ, (Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N v) ξ = q
Langlands.GaloisCohomology.PoitouTate.finite_dualizingModule.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  [NeZero N] (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) :
  Finite ↑(Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
Langlands.GaloisCohomology.PoitouTate.freeOnCosets_of_le.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {i : Ω} (hi : i ^ 2 = -1)
  (hiS : i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) {L₀ : IntermediateField K Ω} [NumberField ↥L₀]
  (hL₀ : ∀ (x : ↥L₀), (algebraMap (↥L₀) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (hL₀i : L₀ = K⟮i⟯)
  (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  (hU : U ≤ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) :
  Langlands.GaloisCohomology.FreeOnCosets (Langlands.GaloisCohomology.PoitouTate.realFamily ι S) ↑U
Langlands.GaloisCohomology.PoitouTate.isSmoothRep_dualRep_dualizingModule_coind.{u} {K Ω : Type u} [Field K]
  [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (U : OpenSubgroup (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) :
  Langlands.IsSmoothRep
    (Langlands.ProfiniteCohomology.dualRep (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
      (Rep.coind.{u, u, u, u} (↑U).subtype (Langlands.ProfiniteCohomology.zmodRep (↥↑U) N)))
Langlands.GaloisCohomology.PoitouTate.isTotallyComplex_of_le.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {i : Ω}
  (hi : i ^ 2 = -1) (hiS : i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) {L₀ : IntermediateField K Ω}
  [NumberField ↥L₀] (hL₀ : ∀ (x : ↥L₀), (algebraMap (↥L₀) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (hL₀i : L₀ = K⟮i⟯) {L : IntermediateField K Ω} [NumberField ↥L]
  (hL : ∀ (x : ↥L), (algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (hU :
    Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL ≤
      Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) :
  NumberField.IsTotallyComplex ↥L
Langlands.GaloisCohomology.PoitouTate.localKummerSequence.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  CategoryTheory.ShortComplex
    (Rep.{u, u, u} (ULift.{u, 0} ℤ)
      Gal(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
            v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
Langlands.GaloisCohomology.PoitouTate.localKummerSequence_shortExact.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  (Langlands.GaloisCohomology.PoitouTate.localKummerSequence ι S N v).ShortExact
Langlands.GaloisCohomology.PoitouTate.surjective_trace.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N] [Finite ↑S]
  (hN : N ≠ 1)
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S) :
  Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.trace ι S N)
```

The real Kummer sequence (namespace `Langlands.GaloisCohomology`): `realKummerSequence ι S N w`, the
sequence `0 → μ_N(K_S) → K̄_wˣ → K̄_wˣ → 0` at an infinite place `w` (smoothness instances
`isSmoothRep_realKummerSequence_X₁`, `_X₂`, `_X₃`), short exact (`realKummerSequence_shortExact`), beside
`localKummerSequence` at the finite places.

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.realKummerSequence.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K) :
  CategoryTheory.ShortComplex (Rep.{u, u, u} (ULift.{u, 0} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion))
Langlands.GaloisCohomology.isSmoothRep_realKummerSequence_X₁.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K) : Langlands.IsSmoothRep (Langlands.GaloisCohomology.realKummerSequence ι S N w).X₁
Langlands.GaloisCohomology.isSmoothRep_realKummerSequence_X₂.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K) : Langlands.IsSmoothRep (Langlands.GaloisCohomology.realKummerSequence ι S N w).X₂
Langlands.GaloisCohomology.isSmoothRep_realKummerSequence_X₃.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ)
  (w : NumberField.InfinitePlace K) : Langlands.IsSmoothRep (Langlands.GaloisCohomology.realKummerSequence ι S N w).X₃
Langlands.GaloisCohomology.realKummerSequence_shortExact.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (N : ℕ) [NeZero N]
  (hS : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S)
  (w : NumberField.InfinitePlace K) : (Langlands.GaloisCohomology.realKummerSequence ι S N w).ShortExact
```

## Outline of the proofs

The local Kummer sequence (`localKummerSequence_shortExact`, from the Kummer sequence of the Library and a count of roots of unity) and the finite invariant of the Library give every invariant of `(1/N)ℤ/ℤ`. The dévissage `TateCompactDualityHypotheses` needs `Ĥ_c⁴ = 0` (hypothesis) and the duality for `Coind_U(ℤ/N)`, `U` fixing `K(i)`: `U` is free on the cosets of the complex conjugations (they send `i` to `-i`), so `bijective_tateCompactDualityMap_coind` reduces to the duality for `ℤ/N` over `U` with the Mackey family, which is that of the totally complex fixed field `L` (`bijective_compactZmodDualityMap_fixingOpenSubgroup` with `FinitePlacesDualityStatement` for `L`); the trace of `U` is surjective (`surjective_trace`, `surjective_tateCompactCores_three`), and the trace of `L` generates the characters of `H_c³` (`exists_eq_mul_of_bijective_zero`, from the cup product with `H⁰`).

## Declarations

`localKummerSequence`, `localKummerSequence_shortExact`, `exists_invariantAt_eq`, `surjective_trace`, `exists_eq_mul_of_bijective_zero`, `conj_realLocalizationHom_closureConj_apply`, `apply_sqrt_neg_one_of_mem`, `freeOnCosets_of_le`, `isTotallyComplex_of_le`, `finite_dualizingModule`, `isSmoothRep_dualRep_dualizingModule_coind`, `bijective_tateCompactDualityMap_coind_fixingOpenSubgroup`, `bijective_dualityMap_of_even`, `realKummerSequence`, `isSmoothRep_realKummerSequence_X₁`, `isSmoothRep_realKummerSequence_X₂`, `isSmoothRep_realKummerSequence_X₃`, `realKummerSequence_shortExact`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
