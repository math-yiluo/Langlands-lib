# The degrees above two and the real places

`Langlands/GaloisCohomology/Global/RealPlaces/HighDegree.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K`, `G_S` the Galois
group of the maximal extension `K_S ⊆ Ω` of `K` unramified outside `S` (ramification at the infinite
places allowed), `ι : PlaceEmbeddings K Ω`, and `M` a finite smooth `G_S`-module killed by `n ≠ 0`
such that every finite place above `n` lies in `S`. For a real place `w`, `realLocalization ι M w r`
is the localization `Hʳ(G_S, M) → Hʳ(K_w, M)` (`Langlands.GaloisCohomology.Global.Localization`).

**Theorems.**
1. (`finite_cohomology`) For finite `S` and `#M` with the places above it in `S`, `Hʳ(G_S, M)` is
   finite for every `r` (NSW (8.3.20) (i)). No hypothesis.
2. (`bijective_realLocalization_of_odd_or_isTotallyComplex`) If `n` is odd or `K` has no real place,
   `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` is bijective for `r ≥ 3`: both sides vanish
   (`cd_ℓ(G_S) ≤ 2` for the primes `ℓ ∣ n`, from `Langlands.GaloisCohomology.Global.Dimension.Proof`;
   the Galois group of a real place has order two, `card_closureGalois`, so its cohomology in positive
   degree is killed by `2`). No hypothesis.
3. (`bijective_realLocalization_of_degreeThree`) **Tate's theorem** (NSW (8.6.10) (ii); Milne, *ADT*, I.4.10 (c)): for
   finite `S` and `#M` with the places above it in `S`, `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` is
   bijective for every `r ≥ 3`, **from the statement `RealLocalizationDegreeThreeStatement`**, which is
   the case `r = 3` (for all number fields, all finite `S` and all such `M`). This file does not prove
   `RealLocalizationDegreeThreeStatement`: both proofs in the literature get the degree `3` from the
   global duality of Poitou–Tate (NSW (8.4.4) with the archimedean duality (7.2.17); Milne I.4.10 from
   the duality for the class formation of `S`-idèle classes). It is proved, from Poitou–Tate duality
   and the vanishing of the cohomology with compact support in degrees `≥ 4`, as
   `realLocalizationDegreeThreeStatement` of
   `Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof`, which also gives the outright
   forms `bijective_realLocalization`, `bijective_realLocalization_of_nsmul`.

**The dimension shift.** If `n` is even, `S` contains the places above `2`, so `K(i) ⊆ K_S`
(`exists_isTotallyComplex_intermediateField`) and `U = G_S(K(i))` is an open subgroup whose fixed field
is totally complex; hence `Hʳ(U, X) = 0` for `r ≥ 3` and every smooth `U`-module `X` killed by `n`
(`subsingleton_cohomology_fixingOpenSubgroup_of_isTotallyComplex`, through `G_S(K(i)) ≅ G_{S'}(K(i))`).
With `0 → M → Ind_U^{G_S} M → B → 0` (`coindUnitSequence`; `B` is finite and killed by `n`):
- by Shapiro's lemma `Hʳ(G_S, Ind_U M) = Hʳ(U, M) = 0` for `r ≥ 3`, so the connecting map
  `Hʳ(G_S, B) → Hʳ⁺¹(G_S, M)` is onto for `r ≥ 2` and bijective for `r ≥ 3`
  (`surjective_δ_coindUnitSequence`, `bijective_δ_of_subsingleton`); this gives the finiteness in
  degrees `≥ 3` from the finiteness in degree `2` (`finite_cohomology_of_le_two_of_nsmul`, from
  `Langlands.GaloisCohomology.Global.Finiteness`);
- at a real place `w`, the image `c` of the complex conjugation is not in `U` (it sends `i` to `-i`,
  `realLocalizationHom_closureConj_apply`), every element of `G_S` lies in `U` or `Uc`
  (`mul_inv_realLocalizationHom_closureConj_mem`), so the restriction of `Ind_U M` to the Galois group
  `{1, c}` of `w` is induced from the trivial group (`bijective_coindRealLocal`) and has no cohomology
  in positive degree (`subsingleton_cohomology_res_coind`);
- the connecting maps commute with the localization (`δ_comp_map` of the foundations), so bijectivity
  in degree `r` for `B` gives bijectivity in degree `r + 1` for `M` (`bijective_realLocalization_succ`),
  and `bijective_realLocalization_of_nsmul_of_degreeThree` follows by induction from degree `3`.

NSW use the module induced from `G(K|k)` for a totally imaginary `K` over which `A` becomes trivial;
here the module is induced from `G_S(K(i))` directly, which needs no triviality because the vanishing
`Hʳ(U, X) = 0`, `r ≥ 3`, holds for every torsion `X` killed by `n`.

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
Langlands.GaloisCohomology.RealLocalizationDegreeThreeStatement : Prop
@Langlands.GaloisCohomology.card_closureGalois : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K), w.IsReal → Nat.card Gal(AlgebraicClosure w.Completion/w.Completion) = 2
@Langlands.GaloisCohomology.two_nsmul_cohomology_closureGalois : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K),
  w.IsReal →
    ∀ (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion))
      [inst_2 : Langlands.IsSmoothRep A] {r : ℕ},
      r ≠ 0 → ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology A r)), 2 • x = 0
@Langlands.GaloisCohomology.eq_zero_cohomology_closureGalois_of_odd : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K),
  w.IsReal →
    ∀ (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion))
      [inst_2 : Langlands.IsSmoothRep A] {n : ℕ},
      Odd n →
        (∀ (a : ↑A), n • a = 0) → ∀ {r : ℕ}, r ≠ 0 → ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology A r)), x = 0
@Langlands.GaloisCohomology.bijective_realLocalization_of_odd_or_isTotallyComplex : ∀ {K : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] {Ω : Type u_1} [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_5 : Langlands.IsSmoothRep M] {n : ℕ},
  n ≠ 0 →
    (∀ (m : ↑M), n • m = 0) →
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
        Odd n ∨ NumberField.IsTotallyComplex K →
          ∀ {r : ℕ},
            3 ≤ r →
              Function.Bijective
                fun (x : ↑(Langlands.ProfiniteCohomology.cohomology M r))
                  (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
                (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
@Langlands.GaloisCohomology.subsingleton_cohomology_fixingOpenSubgroup_of_isTotallyComplex : ∀ {K Ω : Type u_1}
  [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (L : IntermediateField K Ω)
  [inst_5 : NumberField ↥L]
  (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
  NumberField.IsTotallyComplex ↥L →
    ∀ {n : ℕ},
      n ≠ 0 →
        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
          ∀
            (X :
              Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ)
                ↥↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
            [inst_6 : Langlands.IsSmoothRep X],
            (∀ (x : ↑X), n • x = 0) → ∀ {r : ℕ}, 3 ≤ r → Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology X r)
@Langlands.GaloisCohomology.exists_sqrt_neg_one_mem : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S) →
    ∃ (i : Ω), i ^ 2 = -1 ∧ i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S
@Langlands.GaloisCohomology.exists_isTotallyComplex_intermediateField : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S) →
    ∃ (i : Ω) (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ :
      ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
      NumberField.IsTotallyComplex ↥L ∧ i ^ 2 = -1 ∧ i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S ∧ L = K⟮i⟯
@Langlands.GaloisCohomology.coindUnit_injective : ∀ {G : Type u_1} [inst : Group G] (U : Subgroup G)
  (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G),
  Function.Injective ⇑(Rep.Hom.hom (Langlands.ProfiniteCohomology.coindUnit U A))
@Langlands.GaloisCohomology.coindUnitSequence : {G : Type u_1} →
  [inst : Group G] →
    Subgroup G →
      Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G → CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G)
@Langlands.GaloisCohomology.coindUnitSequence_shortExact : ∀ {G : Type u_1} [inst : Group G] (U : Subgroup G)
  (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G), (Langlands.GaloisCohomology.coindUnitSequence U A).ShortExact
@Langlands.GaloisCohomology.isSmoothRep_coindUnitSequence_X₁ : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] (U : OpenSubgroup G) (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G)
  [Langlands.IsSmoothRep A], Langlands.IsSmoothRep (Langlands.GaloisCohomology.coindUnitSequence (↑U) A).X₁
@Langlands.GaloisCohomology.isSmoothRep_coindUnitSequence_X₂ : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G)
  (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [Langlands.IsSmoothRep A],
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.coindUnitSequence (↑U) A).X₂
@Langlands.GaloisCohomology.isSmoothRep_coindUnitSequence_X₃ : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G)
  (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [Langlands.IsSmoothRep A],
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.coindUnitSequence (↑U) A).X₃
@Langlands.GaloisCohomology.finite_coindUnitSequence_X₃ : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G)
  (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [Finite ↑A],
  Finite ↑(Langlands.GaloisCohomology.coindUnitSequence (↑U) A).X₃
@Langlands.GaloisCohomology.nsmul_coindUnitSequence_X₃ : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  (U : OpenSubgroup G) (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) {n : ℕ},
  (∀ (a : ↑A), n • a = 0) → ∀ (b : ↑(Langlands.GaloisCohomology.coindUnitSequence (↑U) A).X₃), n • b = 0
@Langlands.GaloisCohomology.surjective_δ_coindUnitSequence : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] (U : OpenSubgroup G)
  (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_4 : Langlands.IsSmoothRep A] (r : ℕ),
  Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑U).subtype A) (r + 1)) →
    Function.Surjective ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ r (r + 1) ⋯))
@Langlands.GaloisCohomology.injective_δ_coindUnitSequence : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] (U : OpenSubgroup G)
  (A : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_4 : Langlands.IsSmoothRep A] (r : ℕ),
  Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑U).subtype A) r) →
    Function.Injective ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ r (r + 1) ⋯))
@Langlands.GaloisCohomology.two_mem_of_even : ∀ {K : Type u_1} [inst : Field K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {n : ℕ},
  Even n →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑2 ∈ v.asIdeal → v ∈ S
@Langlands.GaloisCohomology.finite_cohomology_of_le_two_of_nsmul : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S] {n : ℕ},
  n ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
      ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
        [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
        (∀ (m : ↑M), n • m = 0) → ∀ r ≤ 2, Finite ↑(Langlands.ProfiniteCohomology.cohomology M r)
@Langlands.GaloisCohomology.finite_cohomology_of_nsmul : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S] {n : ℕ},
  n ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
      ∀ (r : ℕ) (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
        [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
        (∀ (m : ↑M), n • m = 0) → Finite ↑(Langlands.ProfiniteCohomology.cohomology M r)
@Langlands.GaloisCohomology.finite_cohomology : ∀ {K Ω : Type u_1} [inst : Field K] [NumberField K] [inst_2 : Field Ω]
  [inst_3 : Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S]
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S) →
    ∀ (r : ℕ), Finite ↑(Langlands.ProfiniteCohomology.cohomology M r)
@Langlands.GaloisCohomology.apply_sqrt_neg_one : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {i : Ω},
  i ^ 2 = -1 →
    ∀ (hiS : i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
      (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S), g ⟨i, hiS⟩ = ⟨i, hiS⟩ ∨ g ⟨i, hiS⟩ = -⟨i, hiS⟩
@Langlands.GaloisCohomology.mem_fixingOpenSubgroup_of_apply_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {i : Ω}
  (hiS : i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) {L : IntermediateField K Ω} [inst_5 : NumberField ↥L]
  (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
  L = K⟮i⟯ →
    ∀ (g : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S),
      g ⟨i, hiS⟩ = ⟨i, hiS⟩ → g ∈ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL
@Langlands.GaloisCohomology.realLocalizationHom_closureConj_apply : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {i : Ω},
  i ^ 2 = -1 →
    ∀ (hiS : i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      ((Langlands.Galois.realLocalizationHom ι S w) (Langlands.GaloisCohomology.closureConj w hw)) ⟨i, hiS⟩ = -⟨i, hiS⟩
@Langlands.GaloisCohomology.realLocalizationHom_closureConj_not_mem : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {i : Ω},
  i ^ 2 = -1 →
    i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S →
      ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal) {L : IntermediateField K Ω} [inst_5 : NumberField ↥L]
        (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
        L = K⟮i⟯ →
          (Langlands.Galois.realLocalizationHom ι S w) (Langlands.GaloisCohomology.closureConj w hw) ∉
            Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL
@Langlands.GaloisCohomology.mul_inv_realLocalizationHom_closureConj_mem : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {i : Ω},
  i ^ 2 = -1 →
    i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S →
      ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal) {L : IntermediateField K Ω} [inst_5 : NumberField ↥L]
        (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
        L = K⟮i⟯ →
          ∀ g ∉ Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL,
            g * ((Langlands.Galois.realLocalizationHom ι S w) (Langlands.GaloisCohomology.closureConj w hw))⁻¹ ∈
              Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL
@Langlands.GaloisCohomology.bijective_δ_of_subsingleton : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G]
  {X : CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k G)} [inst_4 : Langlands.IsSmoothRep X.X₁]
  [inst_5 : Langlands.IsSmoothRep X.X₂] [inst_6 : Langlands.IsSmoothRep X.X₃] (hX : X.ShortExact) (r : ℕ),
  Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology X.X₂ r) →
    Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology X.X₂ (r + 1)) →
      Function.Bijective ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ hX r (r + 1) ⋯))
@Langlands.GaloisCohomology.coindRealLocal : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [inst_4 : IsSepClosure K Ω] →
            (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
              (ι : Langlands.Galois.PlaceEmbeddings K Ω) →
                {L : IntermediateField K Ω} →
                  [inst_5 : NumberField ↥L] →
                    (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) →
                      (w : NumberField.InfinitePlace K) →
                        (M :
                            Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ)
                              (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) →
                          [Langlands.IsSmoothRep M] →
                            Rep.res (↑(Langlands.Galois.realLocalizationHom ι S w))
                                (Rep.coind.{u_1, u_1, u_1, u_1}
                                  (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                                  (Rep.res
                                    (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                                    M)) ⟶
                              Langlands.ProfiniteCohomology.discreteCoind (ULift.{u_1, 0} ℤ)
                                Gal(AlgebraicClosure w.Completion/w.Completion) ↑M
@Langlands.GaloisCohomology.coindRealLocal_apply : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {L : IntermediateField K Ω} [inst_5 : NumberField ↥L]
  (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S)
  (w : NumberField.InfinitePlace K)
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
  [inst_6 : Langlands.IsSmoothRep M]
  (f :
    ↑(Rep.coind.{u_1, u_1, u_1, u_1} (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
        (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype M)))
  (σ : Gal(AlgebraicClosure w.Completion/w.Completion)),
  ((Rep.Hom.hom (Langlands.GaloisCohomology.coindRealLocal S ι hL w M)) f) σ =
    ↑f ((Langlands.Galois.realLocalizationHom ι S w) σ)
@Langlands.GaloisCohomology.bijective_coindRealLocal : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {i : Ω},
  i ^ 2 = -1 →
    i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S →
      ∀ {L : IntermediateField K Ω} [inst_5 : NumberField ↥L]
        (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
        L = K⟮i⟯ →
          ∀ (w : NumberField.InfinitePlace K),
            w.IsReal →
              ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
                [inst_6 : Langlands.IsSmoothRep M],
                Function.Bijective ⇑(Rep.Hom.hom (Langlands.GaloisCohomology.coindRealLocal S ι hL w M))
@Langlands.GaloisCohomology.subsingleton_cohomology_res_coind : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {i : Ω},
  i ^ 2 = -1 →
    i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S →
      ∀ {L : IntermediateField K Ω} [inst_5 : NumberField ↥L]
        (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
        L = K⟮i⟯ →
          ∀ (w : NumberField.InfinitePlace K),
            w.IsReal →
              ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
                [inst_6 : Langlands.IsSmoothRep M] (q : ℕ),
                Subsingleton
                  ↑(Langlands.ProfiniteCohomology.cohomology
                      (Rep.res (↑(Langlands.Galois.realLocalizationHom ι S w))
                        (Rep.coind.{u_1, u_1, u_1, u_1}
                          (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                          (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)).subtype
                            M)))
                      (q + 1))
@Langlands.GaloisCohomology.bijective_realLocalization_succ : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) {i : Ω},
  i ^ 2 = -1 →
    i ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S →
      ∀ {L : IntermediateField K Ω} [inst_5 : NumberField ↥L]
        (hL : ∀ (x : ↥L), (Algebra.algebraMap (↥L) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S),
        L = K⟮i⟯ →
          NumberField.IsTotallyComplex ↥L →
            ∀ {n : ℕ},
              n ≠ 0 →
                (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
                  ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
                    [inst_6 : Langlands.IsSmoothRep M],
                    (∀ (m : ↑M), n • m = 0) →
                      ∀ {r : ℕ},
                        3 ≤ r →
                          (Function.Bijective
                              fun
                                (x :
                                  ↑(Langlands.ProfiniteCohomology.cohomology
                                      (Langlands.GaloisCohomology.coindUnitSequence
                                          (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL))
                                          M).X₃
                                      r))
                                (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
                              (Langlands.GaloisCohomology.realLocalization ι
                                  (Langlands.GaloisCohomology.coindUnitSequence
                                      (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)) M).X₃
                                  (↑w) r)
                                x) →
                            Function.Bijective
                              fun (x : ↑(Langlands.ProfiniteCohomology.cohomology M (r + 1)))
                                (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
                              (Langlands.GaloisCohomology.realLocalization ι M (↑w) (r + 1)) x
@Langlands.GaloisCohomology.bijective_realLocalization_of_nsmul_of_degreeThree : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Langlands.GaloisCohomology.RealLocalizationDegreeThreeStatement →
    ∀ {n : ℕ},
      n ≠ 0 →
        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑n ∈ v.asIdeal → v ∈ S) →
          ∀ {r : ℕ},
            3 ≤ r →
              ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
                [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
                (∀ (m : ↑M), n • m = 0) →
                  Function.Bijective
                    fun (x : ↑(Langlands.ProfiniteCohomology.cohomology M r))
                      (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
                    (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
@Langlands.GaloisCohomology.bijective_realLocalization_of_degreeThree : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Langlands.GaloisCohomology.RealLocalizationDegreeThreeStatement →
    ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S))
      [inst_6 : Langlands.IsSmoothRep M] [Finite ↑M],
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑(Nat.card ↑M) ∈ v.asIdeal → v ∈ S) →
        ∀ {r : ℕ},
          3 ≤ r →
            Function.Bijective
              fun (x : ↑(Langlands.ProfiniteCohomology.cohomology M r))
                (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
              (Langlands.GaloisCohomology.realLocalization ι M (↑w) r) x
```

## Literature

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VIII §6, (8.6.10)
  Theorem (ii), statement p. 489, proof pp. 490–491 (degree `3` from Poitou–Tate duality; the degrees
  `≥ 4` by the dimension shift with `0 → A → Ind_G A → B → 0`); Chapter VIII §3, (8.3.20) Theorem (i),
  p. 464 (finiteness).
- Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I §4, Theorem 4.10 (c), p. 57.

## Source and licence

New file: no text of the repository `leanprover-community/riemann-hypothesis` is used. The source
proves the same statement (`bijective_gsRealRes`, `src/GroundTheory/ProfiniteCohomology/PoitouTate/
NonemptyOfNatCastMemOfNeOne.lean`, line 142) by another route: injectivity in degree `3` from its
Poitou–Tate hypotheses, and degrees `≥ 4` and surjectivity from the vanishing of Tate-modified
cohomology with compact support (`RealPlaces/Vanishing*.lean`).
