import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearComposition
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion
import Langlands.Geometry.Analytic.NearIdentityDomainRestriction

/-! # Postcomposition of Berkovich's test relations -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Charts

variable {T A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- The image of a chart under a quasi-isomorphism is a chart, and the pullback onto it
represents the whole spectrum. -/
theorem exists_chart_image_of_isQuasiIso {t : T ⟶ A} (ht : t.IsQuasiIso)
    (Q : T.presentation.atlas.Index) :
    ∃ (D : A.presentation.atlas.Index) (hD : t.baseMap '' Set.range (T.presentation.atlas.chart Q) ⊆
        Set.range (A.presentation.atlas.chart D)),
      Set.range (A.presentation.atlas.chart D) =
          t.baseMap '' Set.range (T.presentation.atlas.chart Q) ∧
        PresentedAffinoidAlgebra.Represents K (t.pullback Q D hD) Set.univ := by
  obtain ⟨m, hm⟩ := t.target_exists Q
  obtain ⟨D, hD⟩ := A.hasAllLocalDomains.exists_chart
    (⟨m, ht.localDomain Q m hm⟩ : IndexedAffinoidAtlas.LocalDomain A.presentation.atlas)
  have hDeq : Set.range (A.presentation.atlas.chart D) =
      t.baseMap '' Set.range (T.presentation.atlas.chart Q) := by
    rw [hD]
    change A.presentation.atlas.chart m '' (A.presentation.atlas.chart m ⁻¹'
      (t.baseMap '' Set.range (T.presentation.atlas.chart Q))) = _
    exact Set.image_preimage_eq_of_subset hm
  refine ⟨D, hDeq.symm.subset, hDeq, ?_⟩
  have h := ht.2 Q D hDeq.symm.subset
  have hloc : t.chartImageLocus Q D = Set.univ := by
    unfold AffinoidAtlasPresentation.StrongHom.chartImageLocus
    rw [← hDeq, Set.preimage_range]
  rwa [hloc] at h

/-- Charts mapped into a target chart cover a neighbourhood of a point inside the preimage
of that target chart. -/
theorem exists_charts_nhds_preimage (c : T ⟶ B) (j : B.presentation.atlas.Index)
    {z : T.presentation.space} (hz : c.baseMap z ∈ Set.range (B.presentation.atlas.chart j)) :
    ∃ I : Set T.presentation.atlas.Index, I.Finite ∧
      (∀ k ∈ I, c.baseMap '' Set.range (T.presentation.atlas.chart k) ⊆
        Set.range (B.presentation.atlas.chart j)) ∧
      ∃ O ∈ 𝓝 z, O ∩ c.baseMap ⁻¹' Set.range (B.presentation.atlas.chart j) ⊆
        ⋃ k ∈ I, Set.range (T.presentation.atlas.chart k) := by
  classical
  obtain ⟨σ, hσfin, hσ, hzσ, hσn⟩ := T.presentation.atlas.isNet_chartFamily.1 z
  have key : ∀ V ∈ σ, ∃ J : Set T.presentation.atlas.Index, J.Finite ∧
      (∀ k ∈ J, c.baseMap '' Set.range (T.presentation.atlas.chart k) ⊆
        Set.range (B.presentation.atlas.chart j)) ∧
      ∃ W ∈ 𝓝 (c.baseMap z), ∀ y ∈ V, c.baseMap y ∈ W →
        c.baseMap y ∈ Set.range (B.presentation.atlas.chart j) →
          ∃ k ∈ J, y ∈ Set.range (T.presentation.atlas.chart k) := by
    intro V hV
    obtain ⟨k, rfl⟩ := hσ hV
    obtain ⟨m, hkm⟩ := c.target_exists k
    have hzm : c.baseMap z ∈ Set.range (B.presentation.atlas.chart m) := hkm ⟨z, hzσ _ hV, rfl⟩
    obtain ⟨σ', hσ'fin, hσ', hzσ', hσ'n⟩ := B.presentation.atlas.isNet_chartFamily.2 _
      (Set.mem_range_self j) _ (Set.mem_range_self m) ⟨c.baseMap z, hz, hzm⟩
    obtain ⟨W, hW, hWsub⟩ := (mem_nhds_subtype _ _ _).mp hσ'n
    have key2 : ∀ W' ∈ σ', ∃ q : T.presentation.atlas.Index,
        c.baseMap '' Set.range (T.presentation.atlas.chart q) ⊆
          Set.range (B.presentation.atlas.chart j) ∧
        ∀ y ∈ Set.range (T.presentation.atlas.chart k),
          (∃ h : c.baseMap y ∈ Set.range (B.presentation.atlas.chart j) ∩
            Set.range (B.presentation.atlas.chart m), (⟨c.baseMap y, h⟩ : _) ∈ W') →
          y ∈ Set.range (T.presentation.atlas.chart q) := by
      intro W' hW'
      obtain ⟨V', ⟨l, rfl⟩, hVsub, rfl⟩ := hσ' hW'
      obtain ⟨q, hq⟩ := AffinoidAtlasPresentation.StrongHom.exists_chart_inter_preimage c
        T.hasAllLocalDomains k m l hkm (fun _ h => (hVsub h).2)
      refine ⟨q, ?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        rw [hq] at hx
        exact (hVsub hx.2).1
      · rintro y hy ⟨h, hyl⟩
        rw [hq]
        exact ⟨hy, hyl⟩
    choose q hqj hqcov using key2
    refine ⟨{k' | ∃ W' hW', q W' hW' = k'}, hσ'fin.dependent_image q, ?_, W, hW, ?_⟩
    · rintro _ ⟨W', hW', rfl⟩
      exact hqj W' hW'
    · intro y hy hyW hyj
      have hym : c.baseMap y ∈ Set.range (B.presentation.atlas.chart m) := hkm ⟨y, hy, rfl⟩
      have hmem : (⟨c.baseMap y, hyj, hym⟩ : _) ∈ ⋃₀ σ' := hWsub hyW
      obtain ⟨W', hW', hyW'⟩ := hmem
      exact ⟨q W' hW', ⟨W', hW', rfl⟩, hqcov W' hW' y hy ⟨⟨hyj, hym⟩, hyW'⟩⟩
  choose J hJfin hJ W hW hWcov using key
  have : Finite σ := hσfin.to_subtype
  refine ⟨⋃ V : σ, J V.1 V.2, Set.finite_iUnion fun V => hJfin V.1 V.2, ?_,
    ⋃₀ σ ∩ ⋂ V : σ, c.baseMap ⁻¹' W V.1 V.2, ?_, ?_⟩
  · intro k hk
    obtain ⟨V, hV⟩ := Set.mem_iUnion.mp hk
    exact hJ V.1 V.2 k hV
  · refine Filter.inter_mem hσn (Filter.iInter_mem.mpr fun V => ?_)
    exact c.baseMap.continuous.continuousAt.preimage_mem_nhds (hW V.1 V.2)
  · rintro y ⟨⟨⟨V, hV, hyV⟩, hyW⟩, hyj⟩
    have hyW' : c.baseMap y ∈ W V hV := Set.mem_iInter.mp hyW ⟨V, hV⟩
    obtain ⟨k, hk, hyk⟩ := hWcov V hV y hyV hyW' hyj
    exact Set.mem_biUnion (Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hk⟩) hyk

/-- A compact preimage of a target chart is covered by finitely many source charts mapped into
the target chart. -/
theorem exists_finite_charts_cover_preimage (c : T ⟶ B) (j : B.presentation.atlas.Index)
    (hK : IsCompact (c.baseMap ⁻¹' Set.range (B.presentation.atlas.chart j))) :
    ∃ I : Finset T.presentation.atlas.Index,
      (∀ k ∈ I, c.baseMap '' Set.range (T.presentation.atlas.chart k) ⊆
        Set.range (B.presentation.atlas.chart j)) ∧
      c.baseMap ⁻¹' Set.range (B.presentation.atlas.chart j) ⊆
        ⋃ k ∈ I, Set.range (T.presentation.atlas.chart k) := by
  classical
  choose I hIfin hI O hO hOsub using
    fun z : c.baseMap ⁻¹' Set.range (B.presentation.atlas.chart j) =>
      exists_charts_nhds_preimage c j z.2
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun z hz => O ⟨z, hz⟩) (fun z hz => hO ⟨z, hz⟩)
  have hfin : (⋃ z ∈ t, I z).Finite := t.finite_toSet.biUnion fun z _ => hIfin z
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro k hk
    rw [Set.Finite.mem_toFinset] at hk
    obtain ⟨z, -, hkz⟩ := Set.mem_iUnion₂.mp hk
    exact hI z k hkz
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (ht hy)
    obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.mp (hOsub z ⟨hyz, hy⟩)
    exact Set.mem_iUnion₂.mpr ⟨k, (Set.Finite.mem_toFinset hfin).mpr
      (Set.mem_iUnion₂.mpr ⟨z, hz, hk⟩), hyk⟩

end Charts

section Strong

variable {S T A B : SaturatedAtlasPresentation.{u, v, w} K}

theorem image_subset_of_comp_image_subset {α : S ⟶ T} {t : T ⟶ A}
    (ht : Function.Injective t.baseMap) {R : Set S.presentation.space}
    {Q : Set T.presentation.space} (h : (α ≫ t).baseMap '' R ⊆ t.baseMap '' Q) :
    α.baseMap '' R ⊆ Q := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨q, hq, he⟩ := h ⟨y, hy, rfl⟩
  exact ht he ▸ hq

/-- **Postcomposition of the test relation, strong form.** Let `t` be injective on points and
let finitely many charts `Q i` of `T`, mapped by `c` into the domain of `τ'`, cover the preimage
of that domain. If charts `D i` of `A` are the images `t(Q i)` and the functions `G i` on them
pull back along `t` to the pullbacks of the function of `τ'` along `c`, then the test relations
for the triples `(D i, G i, t')` between `α ≫ t` and `β ≫ t` give the test relation for `τ'`
between `α ≫ c` and `β ≫ c`. -/
theorem StrongNear.postcomp {ι : Type*} {t : T ⟶ A} (ht : Function.Injective t.baseMap)
    (c : T ⟶ B) (τ' : TestTriple B)
    (Q : ι → T.presentation.atlas.Index) (D : ι → A.presentation.atlas.Index)
    (hD : ∀ i, Set.range (A.presentation.atlas.chart (D i)) =
      t.baseMap '' Set.range (T.presentation.atlas.chart (Q i)))
    (hQ : ∀ i, c.baseMap '' Set.range (T.presentation.atlas.chart (Q i)) ⊆
      Set.range (B.presentation.atlas.chart τ'.domain))
    (hcov : c.baseMap ⁻¹' τ'.locus ⊆ ⋃ i, Set.range (T.presentation.atlas.chart (Q i)))
    (G : ∀ i, A.presentation.atlas.algebra (D i))
    (hG : ∀ i, t.pullback (Q i) (D i) (hD i).symm.subset (G i) =
      c.pullback (Q i) τ'.domain (hQ i) τ'.function)
    {α β : S ⟶ T}
    (h : ∀ i, StrongNear ⟨D i, G i, τ'.bound, τ'.bound_pos⟩ (α ≫ t) (β ≫ t)) :
    StrongNear τ' (α ≫ c) (β ≫ c) := by
  have hmem : ∀ (γ : S ⟶ T) (i) (y : S.presentation.space),
      (γ ≫ t).baseMap y ∈ Set.range (A.presentation.atlas.chart (D i)) ↔
        γ.baseMap y ∈ Set.range (T.presentation.atlas.chart (Q i)) := by
    intro γ i y
    rw [hD i]
    constructor
    · rintro ⟨q, hq, he⟩
      exact ht he ▸ hq
    · intro hy
      exact ⟨_, hy, rfl⟩
  have hpre : ∀ γ : S ⟶ T, (γ ≫ c).baseMap ⁻¹' τ'.locus =
      ⋃ i, (γ ≫ t).baseMap ⁻¹' Set.range (A.presentation.atlas.chart (D i)) := by
    intro γ
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
      exact ⟨i, (hmem γ i y).mpr hi⟩
    · rintro ⟨i, hi⟩
      exact hQ i ⟨γ.baseMap y, (hmem γ i y).mp hi, rfl⟩
  refine ⟨?_, fun y hy => ?_, fun P hP p => ?_⟩
  · rw [hpre α, hpre β]
    exact Set.iUnion_congr fun i => (h i).1
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
    obtain ⟨P, hP, hyP⟩ := (h i).2.1 y ((hmem α i y).mpr hi)
    refine ⟨P, ⟨?_, ?_⟩, hyP⟩
    · refine (Set.image_comp c.baseMap α.baseMap _).subset.trans ?_
      exact (Set.image_mono (image_subset_of_comp_image_subset ht ((hD i) ▸ hP.1))).trans (hQ i)
    · refine (Set.image_comp c.baseMap β.baseMap _).subset.trans ?_
      exact (Set.image_mono (image_subset_of_comp_image_subset ht ((hD i) ▸ hP.2))).trans (hQ i)
  · set y := S.presentation.atlas.chart P p
    have hyc : (α ≫ c).baseMap y ∈ τ'.locus := hP.1 ⟨y, ⟨p, rfl⟩, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hyc)
    obtain ⟨P₁, hP₁, hyP₁⟩ := (h i).2.1 y ((hmem α i y).mpr hi)
    obtain ⟨P', hyP', hP'sub⟩ := exists_chart_mem_subset_inter S P P₁ ⟨p, rfl⟩ hyP₁
    obtain ⟨p', rfl⟩ := exists_restriction_comap_eq (fun _ h => (hP'sub h).1) p hyP'
    have hP'P₁ : Set.range (S.presentation.atlas.chart P') ⊆
        Set.range (S.presentation.atlas.chart P₁) := fun _ h => (hP'sub h).2
    have hαt : (α ≫ t).baseMap '' Set.range (S.presentation.atlas.chart P') ⊆
        Set.range (A.presentation.atlas.chart (D i)) := (Set.image_mono hP'P₁).trans hP₁.1
    have hβt : (β ≫ t).baseMap '' Set.range (S.presentation.atlas.chart P') ⊆
        Set.range (A.presentation.atlas.chart (D i)) := (Set.image_mono hP'P₁).trans hP₁.2
    have hαQ := image_subset_of_comp_image_subset ht ((hD i) ▸ hαt)
    have hβQ := image_subset_of_comp_image_subset ht ((hD i) ▸ hβt)
    have hαc : (α ≫ c).baseMap '' Set.range (S.presentation.atlas.chart P') ⊆
        Set.range (B.presentation.atlas.chart τ'.domain) :=
      (Set.image_mono fun _ h => (hP'sub h).1).trans hP.1
    have hβc : (β ≫ c).baseMap '' Set.range (S.presentation.atlas.chart P') ⊆
        Set.range (B.presentation.atlas.chart τ'.domain) :=
      (Set.image_mono fun _ h => (hP'sub h).1).trans hP.2
    have hres : Set.range (S.presentation.atlas.chart P') ⊆
        Set.range (S.presentation.atlas.chart P) := fun _ h => (hP'sub h).1
    change p' ((S.presentation.atlas.restriction P' P hres)
      ((α ≫ c).pullback P τ'.domain hP.1 τ'.function -
        (β ≫ c).pullback P τ'.domain hP.2 τ'.function)) ≤ τ'.bound
    rw [map_sub]
    change p' ((S.presentation.atlas.restriction P' P hres).comp
      ((α ≫ c).pullback P τ'.domain hP.1) τ'.function -
        (S.presentation.atlas.restriction P' P hres).comp
          ((β ≫ c).pullback P τ'.domain hP.2) τ'.function) ≤ τ'.bound
    rw [restriction_comp_pullback (α ≫ c) hres τ'.domain hP.1 hαc,
      restriction_comp_pullback (β ≫ c) hres τ'.domain hP.2 hβc,
      comp_pullback_eq α c P' (Q i) τ'.domain hαQ (hQ i) hαc,
      comp_pullback_eq β c P' (Q i) τ'.domain hβQ (hQ i) hβc]
    change p' (α.pullback P' (Q i) hαQ (c.pullback (Q i) τ'.domain (hQ i) τ'.function) -
      β.pullback P' (Q i) hβQ (c.pullback (Q i) τ'.domain (hQ i) τ'.function)) ≤ τ'.bound
    rw [← hG i]
    change p' ((α.pullback P' (Q i) hαQ).comp (t.pullback (Q i) (D i) (hD i).symm.subset) (G i) -
      (β.pullback P' (Q i) hβQ).comp (t.pullback (Q i) (D i) (hD i).symm.subset) (G i)) ≤
        τ'.bound
    rw [← comp_pullback_eq α t P' (Q i) (D i) hαQ (hD i).symm.subset hαt,
      ← comp_pullback_eq β t P' (Q i) (D i) hβQ (hD i).symm.subset hβt]
    exact (h i).2.2 P' ⟨hαt, hβt⟩ p'

/-- Two strong maps can be lifted simultaneously through a quasi-isomorphism after a common
quasi-isomorphic refinement. -/
theorem exists_two_ore (x₀ x₁ : S ⟶ A) (t : T ⟶ A) (ht : t.IsQuasiIso) :
    ∃ (S' : SaturatedAtlasPresentation.{u, v, w} K) (u : S' ⟶ S) (_ : u.IsQuasiIso)
      (α β : S' ⟶ T), α ≫ t = u ≫ x₀ ∧ β ≫ t = u ≫ x₁ := by
  have h₁ := quasiIsoOre_square x₀ t ht
  have h₂ := quasiIsoOre_square (quasiIsoOreInclusion x₀ t ht ≫ x₁) t ht
  refine ⟨_, quasiIsoOreInclusion (quasiIsoOreInclusion x₀ t ht ≫ x₁) t ht ≫
      quasiIsoOreInclusion x₀ t ht,
    (quasiIsomorphisms (K := K)).comp_mem _ _ (isQuasiIso_quasiIsoOreInclusion _ t ht)
      (isQuasiIso_quasiIsoOreInclusion _ t ht),
    quasiIsoOreInclusion (quasiIsoOreInclusion x₀ t ht ≫ x₁) t ht ≫ quasiIsoOreLift x₀ t ht,
    quasiIsoOreLift (quasiIsoOreInclusion x₀ t ht ≫ x₁) t ht, ?_, ?_⟩
  · simp only [Category.assoc, h₁]
  · rw [h₂, Category.assoc]

end Strong

section Localized

variable {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- **Postcomposition of test relations**, for images of saturated presentations. -/
theorem exists_nearNumerators_postcomp (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (τ' : TestTriple B)
    (hK : IsCompact ((localizedSpaceFunctor.map f : localizedSpaceFunctor.obj
      (localizationFunctor.obj A) → localizedSpaceFunctor.obj (localizationFunctor.obj B)) ⁻¹'
        τ'.locus)) :
    ∃ E : Finset (TestTriple A),
      (∀ τ ∈ E, τ.locus ⊆ (localizedSpaceFunctor.map f : localizedSpaceFunctor.obj
        (localizationFunctor.obj A) → localizedSpaceFunctor.obj (localizationFunctor.obj B)) ⁻¹'
          τ'.locus) ∧
      ∀ (C : SaturatedAtlasPresentation.{u, v, w} K)
        (φ ψ : localizationFunctor.obj C ⟶ localizationFunctor.obj A),
        (∀ τ ∈ E, NearNumerators τ φ ψ) → NearNumerators τ' (φ ≫ f) (ψ ≫ f) := by
  classical
  obtain ⟨T, t, ht, c, -, hc, -⟩ := exists_commonStrongNumerators f (𝟙 (localizationFunctor.obj A))
  have hpt := numerator_point_eq_of_fraction_equation t c f hc
  have hKc : IsCompact (c.baseMap ⁻¹' τ'.locus) := by
    have : c.baseMap ⁻¹' τ'.locus = t.baseMap ⁻¹' ((localizedSpaceFunctor.map f :
        localizedSpaceFunctor.obj (localizationFunctor.obj A) →
          localizedSpaceFunctor.obj (localizationFunctor.obj B)) ⁻¹' τ'.locus) := by
      ext x
      exact Iff.of_eq (congrArg (fun z => z ∈ τ'.locus) (hpt x)).symm
    rw [this]
    exact ((IsHomeomorph.homeomorph _ ht.1).isCompact_preimage).mpr hK
  obtain ⟨I, hIgood, hIcov⟩ := exists_finite_charts_cover_preimage c τ'.domain hKc
  choose D hDsub hDeq hDrep using fun k : I => exists_chart_image_of_isQuasiIso ht (k : _)
  let G : ∀ k : I, A.presentation.atlas.algebra (D k) := fun k =>
    (hDrep k).univInverse (c.pullback k τ'.domain (hIgood k k.2) τ'.function)
  have hG : ∀ k : I, t.pullback k (D k) (hDeq k).symm.subset (G k) =
      c.pullback k τ'.domain (hIgood k k.2) τ'.function := fun k =>
    congrArg (fun q => q (c.pullback k τ'.domain (hIgood k k.2) τ'.function))
      (hDrep k).comp_univInverse
  let τ : I → TestTriple A := fun k => ⟨D k, G k, τ'.bound, τ'.bound_pos⟩
  refine ⟨Finset.univ.image τ, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hσ
    change Set.range (A.presentation.atlas.chart (D k)) ⊆ _
    rw [hDeq k]
    rintro _ ⟨x, hx, rfl⟩
    exact (Iff.of_eq (congrArg (fun z => z ∈ τ'.locus) (hpt x))).mpr
      (hIgood k k.2 ⟨x, hx, rfl⟩)
  · intro C φ ψ hE
    obtain ⟨S, s, hs, x₀, x₁, x₂, h0, h1, h2, hn⟩ :=
      exists_strongNear_numerators_aux (Finset.univ.image τ) φ ψ ψ hE hE
    obtain ⟨S', u, hu, α, β, hα, hβ⟩ := exists_two_ore x₀ x₁ t ht
    refine ⟨S', u ≫ s, (quasiIsomorphisms (K := K)).comp_mem _ _ hu hs, α ≫ c, β ≫ c, ?_, ?_, ?_⟩
    · calc localizationFunctor.map (u ≫ s) ≫ φ ≫ f
          = localizationFunctor.map (u ≫ x₀) ≫ f := by
            simp only [Functor.map_comp, Category.assoc, reassoc_of% h0]
        _ = localizationFunctor.map (α ≫ t) ≫ f := by rw [hα]
        _ = localizationFunctor.map (α ≫ c) := by
            rw [Functor.map_comp, Category.assoc, hc, ← Functor.map_comp]
    · calc localizationFunctor.map (u ≫ s) ≫ ψ ≫ f
          = localizationFunctor.map (u ≫ x₁) ≫ f := by
            simp only [Functor.map_comp, Category.assoc, reassoc_of% h1]
        _ = localizationFunctor.map (β ≫ t) ≫ f := by rw [hβ]
        _ = localizationFunctor.map (β ≫ c) := by
            rw [Functor.map_comp, Category.assoc, hc, ← Functor.map_comp]
    · refine StrongNear.postcomp ht.1.injective c τ' (fun k : I => (k : T.presentation.atlas.Index))
        D hDeq (fun k => hIgood k k.2) ?_ G hG fun k => ?_
      · intro y hy
        obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.mp (hIcov hy)
        exact Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hyk⟩
      · rw [hα, hβ]
        exact (hn (τ k) (Finset.mem_image_of_mem τ (Finset.mem_univ k))).1.precomp u

end Localized

/-- **Postcomposition of test relations.** Let `f : V ⟶ U` and let `τ'` be a test triple on
`U` whose preimage under `f` is compact. There is a finite set `E` of test triples on `V`, with
domains inside that preimage, such that `E`-near morphisms to `V` have `τ'`-near composites
with `f`. -/
theorem exists_isNear_postcomp {V U : LocalizedCategory.{u, v, w} (K := K)} (f : V ⟶ U)
    (τ' : TestTriple (presentationOf U))
    (hK : IsCompact ((localizedSpaceFunctor.map f : localizedSpaceFunctor.obj V →
      localizedSpaceFunctor.obj U) ⁻¹' τ'.locus)) :
    ∃ E : Finset (TestTriple (presentationOf V)),
      (∀ τ ∈ E, τ.locus ⊆ (localizedSpaceFunctor.map f : localizedSpaceFunctor.obj V →
        localizedSpaceFunctor.obj U) ⁻¹' τ'.locus) ∧
      ∀ (W : LocalizedCategory.{u, v, w} (K := K)) (φ ψ : W ⟶ V),
        (∀ τ ∈ E, IsNear τ φ ψ) → IsNear τ' (φ ≫ f) (ψ ≫ f) := by
  obtain ⟨E, hEloc, hE⟩ :=
    exists_nearNumerators_postcomp (A := presentationOf V) (B := presentationOf U) f τ' hK
  refine ⟨E, hEloc, fun W φ ψ h => ?_⟩
  exact (isNear_iff_numerators τ' _ _).2 (hE (presentationOf W) φ ψ fun τ hτ =>
    (isNear_iff_numerators τ φ ψ).1 (h τ hτ))

end Langlands.Analytic.SaturatedAtlasPresentation
