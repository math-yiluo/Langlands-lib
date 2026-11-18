import Langlands.Geometry.Analytic.QuasiEtaleRigidity.UnramifiedRigidity
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.ChartCoverRigidity
import Langlands.Geometry.Analytic.EtaleSite
import Langlands.Geometry.Analytic.RecognizedOriginalDomains
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion

/-! # Rigidity of étale strong maps over compact analytic domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, v} K}

/-- A chart `c` of the saturation of `A` on which a strong map `g` is rigid: there are finitely
many functions on `c` and a bound such that two strong maps sending a source chart into `c`,
with the same composite with `g`, whose pullbacks of these functions differ by at most the bound
at every point, have the same pullbacks. -/
def IsRigidChart (g : ofSaturation A ⟶ ofSaturation B)
    (c : (ofSaturation A).presentation.atlas.Index) : Prop :=
  ∃ (F : Finset ((ofSaturation A).presentation.atlas.algebra c)) (δ : ℝ), 0 < δ ∧
    ∀ (S : SaturatedAtlasPresentation.{u, v, v} K) (x₁ x₂ : S ⟶ ofSaturation A)
      (P : S.presentation.atlas.Index)
      (h₁ : x₁.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
        Set.range ((ofSaturation A).presentation.atlas.chart c))
      (h₂ : x₂.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
        Set.range ((ofSaturation A).presentation.atlas.chart c)),
      x₁ ≫ g = x₂ ≫ g →
      (∀ f ∈ F, ∀ p : BanachSpectrum (S.presentation.atlas.algebra P),
        p (x₁.pullback P c h₁ f - x₂.pullback P c h₂ f) ≤ δ) →
      x₁.pullback P c h₁ = x₂.pullback P c h₂

/-- **Rigid charts from unramifiedness.** Let `V'` be a recognized affinoid subset of the
saturation of `A`, with a map `f : R → O(V')` of finite type and `e` killing `Ω[O(V')⁄R]`.
A chart `c` inside `V'`, mapped by `g` into a chart `w` compatibly with `f`, on which `|e| ≥ r`
for some `r > 0`, is rigid. -/
theorem isRigidChart_of_unramified (g : ofSaturation A ⟶ ofSaturation B)
    (V' : A.atlas.saturatedAtlas.RecognizedSubset) {R : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K R V'.algebra) (hft : f.toAlgHom.toRingHom.FiniteType) (e : V'.algebra)
    (he : letI : Algebra R V'.algebra := f.toAlgHom.toRingHom.toAlgebra
      e ∈ Module.annihilator V'.algebra Ω[V'.algebra⁄R])
    {r : ℝ} (hr : 0 < r) (c : (ofSaturation A).presentation.atlas.Index)
    (hcV : Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆ V'.locus)
    (w : (ofSaturation B).presentation.atlas.Index)
    (hcw : g.baseMap '' Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆
      Set.range ((ofSaturation B).presentation.atlas.chart w))
    (ρ : BoundedAlgHom K R ((ofSaturation B).presentation.atlas.algebra w))
    (hcompat : (V'.originalRestriction c hcV).comp f = (g.pullback c w hcw).comp ρ)
    (hce : ∀ z (hz : z ∈ Set.range ((ofSaturation A).presentation.atlas.chart c)),
      r ≤ V'.coordinates ⟨z, hcV hz⟩ e) :
    IsRigidChart g c := by
  classical
  obtain ⟨G, n, M, hM, hcore⟩ := QuasiEtaleRigidity.exists_unramified_rigidity_bound f hft e he
  set res := V'.originalRestriction c hcV
  have hδ : 0 < r ^ n / (2 * (M * G.card + 1)) := by positivity
  refine ⟨G.image res, r ^ n / (2 * (M * G.card + 1)), hδ, ?_⟩
  intro S x₁ x₂ P h₁ h₂ hg hF
  have hcomp : ∀ (x : S ⟶ ofSaturation A)
      (hx : x.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
        Set.range ((ofSaturation A).presentation.atlas.chart c)),
      (x ≫ g).baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
        Set.range ((ofSaturation B).presentation.atlas.chart w) := by
    intro x hx
    rintro _ ⟨z, hz, rfl⟩
    exact hcw ⟨x.baseMap z, hx ⟨z, hz, rfl⟩, rfl⟩
  have hR : ∀ (x : S ⟶ ofSaturation A) hx (a : R),
      x.pullback P c hx (res (f a)) = (x ≫ g).pullback P w (hcomp x hx) (ρ a) := by
    intro x hx a
    have h1 : res (f a) = g.pullback c w hcw (ρ a) := congrArg (fun q => q a) hcompat
    have h2 : (x ≫ g).pullback P w (hcomp x hx) (ρ a) =
        x.pullback P c hx (g.pullback c w hcw (ρ a)) :=
      congrArg (fun q => q (ρ a)) (comp_pullback_eq x g P c w hx hcw (hcomp x hx))
    exact (h2.trans (congrArg (fun z => x.pullback P c hx z) h1.symm)).symm
  have hφ : (x₁.pullback P c h₁).comp res = (x₂.pullback P c h₂).comp res := by
    refine hcore (S.presentation.atlas.algebra P) _ _ (fun a => ?_) (fun x => ?_)
    · change x₁.pullback P c h₁ (res (f a)) = x₂.pullback P c h₂ (res (f a))
      rw [hR x₁ h₁ a, hR x₂ h₂ a]
      exact congrArg (fun q => q (ρ a)) (pullback_congr hg P w (hcomp x₁ h₁) (hcomp x₂ h₂))
    · set q := BanachSpectrum.comap (x₁.pullback P c h₁).toBoundedRingHom x
      have hval : x ((x₁.pullback P c h₁).comp res e) =
          V'.coordinates ⟨(ofSaturation A).presentation.atlas.chart c q, hcV ⟨q, rfl⟩⟩ e := by
        change (BanachSpectrum.comap res.toBoundedRingHom q) e = _
        rw [V'.comap_originalRestriction c hcV q]
        rfl
      have hge : r ≤ x ((x₁.pullback P c h₁).comp res e) := by
        rw [hval]
        exact hce _ ⟨q, rfl⟩
      have hterm : ∀ g' ∈ G, x ((x₁.pullback P c h₁).comp res g' -
          (x₂.pullback P c h₂).comp res g') ≤ r ^ n / (2 * (M * G.card + 1)) := fun g' hg' =>
        hF (res g') (Finset.mem_image_of_mem res hg') x
      have hsum : ∑ g' ∈ G, x ((x₁.pullback P c h₁).comp res g' -
          (x₂.pullback P c h₂).comp res g') ≤ G.card * (r ^ n / (2 * (M * G.card + 1))) := by
        have := Finset.sum_le_card_nsmul G _ _ hterm
        rwa [nsmul_eq_mul] at this
      have hrn : 0 < r ^ n := pow_pos hr n
      have hpow : r ^ n ≤ x ((x₁.pullback P c h₁).comp res e) ^ n :=
        pow_le_pow_left₀ hr.le hge n
      have hMG : 0 ≤ M * G.card := mul_nonneg hM (Nat.cast_nonneg _)
      calc M * ∑ g' ∈ G, x ((x₁.pullback P c h₁).comp res g' -
            (x₂.pullback P c h₂).comp res g')
          ≤ M * (G.card * (r ^ n / (2 * (M * G.card + 1)))) :=
            mul_le_mul_of_nonneg_left hsum hM
        _ = (M * G.card) / (2 * (M * G.card + 1)) * r ^ n := by ring
        _ < 1 * r ^ n := by
            refine mul_lt_mul_of_pos_right ?_ hrn
            rw [div_lt_one (by positivity)]
            linarith
        _ ≤ _ := by rw [one_mul]; exact hpow
  exact Represents.hom_ext (V'.originalRestriction_represents c hcV) _ _ _ hφ

/-- **Local rigid charts.** For an étale strong map `g` and an analytic domain `D` of the
saturation of `A`, every point of `D` has a neighbourhood whose trace on `D` is covered by
finitely many rigid charts contained in `D`. -/
theorem isLocallyChartCovered_isRigidChart (g : ofSaturation A ⟶ ofSaturation B)
    (hg : AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces (A := A) (B := B) g)
    (D : (ofSaturation A).AnalyticDomain) {y : (ofSaturation A).presentation.space}
    (hy : y ∈ D.carrier) :
    (ofSaturation A).IsLocallyChartCovered (IsRigidChart g) D.carrier y := by
  classical
  obtain ⟨V₀, -, hyV₀, hV₀⟩ := hg y
  obtain ⟨Vy, Uy, hVy, hUy, hyVy, hfinite, hpieces⟩ := (hV₀ y hyV₀).1
  have hgyU : g.baseMap y ∈ Uy := hfinite.1 ⟨y, hyVy, rfl⟩
  obtain ⟨I, hIfin, hImem, hInhds⟩ :=
    IndexedAffinoidAtlas.HasAllLocalDomains.exists_finite_chart_nhds_subset
      (ofSaturation B).presentation.atlas (ofSaturation B).hasAllLocalDomains (g.baseMap y) Uy
      (hUy.mem_nhds hgyU)
  have key : ∀ w ∈ I, ∃ (R O : Set (ofSaturation A).presentation.space), R ⊆ D.carrier ∧
      O ∈ 𝓝 y ∧
      D.carrier ∩ g.baseMap ⁻¹' Set.range ((ofSaturation B).presentation.atlas.chart w) ∩ O ⊆
        R ∧ (ofSaturation A).IsLocallyChartCovered (IsRigidChart g) R y := by
    intro w hw
    let W := B.atlas.saturatedAtlas.originalRecognitionIndex w
    have hWlocus : W.locus = Set.range ((ofSaturation B).presentation.atlas.chart w) :=
      W.range_chart.symm.trans (B.atlas.saturatedAtlas.recognitionAtlas_original_range w)
    have hWU : W.locus ⊆ Uy := hWlocus ▸ (hImem w hw).2
    have hgyW : g.baseMap y ∈ W.locus := hWlocus ▸ (hImem w hw).1
    obtain ⟨V', hVW, hV'eq, hfin⟩ := hfinite.2 W hWU
    have hyV' : y ∈ V'.locus := by
      rw [hV'eq]
      exact ⟨hyVy, hgyW⟩
    let s := V'.coordinates ⟨y, hyV'⟩
    have hs : V'.chart s = y := by
      change (V'.coordinates.symm s).val = y
      rw [V'.coordinates.symm_apply_apply]
    have hun := hpieces W hWU hgyW V' hVW hV'eq s hs
    unfold BoundedAlgHom.IsUnramifiedAtPoint at hun
    obtain ⟨e, he, hes⟩ := SetLike.not_le_iff_exists.mp hun
    have hes0 : 0 < s e := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hes)
    have hcont : Continuous fun z : V'.locus => V'.coordinates z e :=
      (BanachSpectrum.evaluation e).continuous.comp V'.coordinates.continuous
    obtain ⟨O₁, hO₁, hO₁eq⟩ := isOpen_induced_iff.mp
      (isOpen_lt continuous_const hcont : IsOpen {z : V'.locus | s e / 2 < V'.coordinates z e})
    have hyO₁ : y ∈ O₁ := by
      have : (⟨y, hyV'⟩ : V'.locus) ∈ Subtype.val ⁻¹' O₁ := by
        rw [hO₁eq]
        exact half_lt_self hes0
      exact this
    have hOnhds : Vy ∩ O₁ ∈ 𝓝 y := (hVy.inter hO₁).mem_nhds ⟨hyVy, hyO₁⟩
    refine ⟨D.carrier ∩ g.baseMap ⁻¹' Set.range ((ofSaturation B).presentation.atlas.chart w) ∩
      (Vy ∩ O₁), Vy ∩ O₁, fun z hz => hz.1.1, hOnhds, fun z hz => hz, ?_⟩
    refine (((isLocallyChartCovered_analyticDomain D hy).inter
      (isLocallyChartCovered_preimage g w (hImem w hw).1)).inter
        (isLocallyChartCovered_of_mem_nhds hOnhds)).of_subset_pred fun c hc => ?_
    have hcV : Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆ V'.locus := by
      intro z hz
      rw [hV'eq]
      exact ⟨(hc hz).2.1, hWlocus ▸ (hc hz).1.2⟩
    have hcw : g.baseMap '' Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆
        Set.range ((ofSaturation B).presentation.atlas.chart w) := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hc hz).1.2
    have hwW : Set.range (B.atlas.saturatedAtlas.chart w) ⊆ W.locus := hWlocus.symm.subset
    refine isRigidChart_of_unramified g V' _ hfin.finite.finiteType e he (half_pos hes0) c hcV w
      hcw (W.originalRestriction w hwW)
      (AffinoidAtlasPresentation.StrongHom.originalRestriction_comp_fullRecognitionPairs g V' W
        hVW c hcV w hwW hcw) fun z hz => ?_
    have : (⟨z, hcV hz⟩ : V'.locus) ∈ Subtype.val ⁻¹' O₁ := (hc hz).2.2
    rw [hO₁eq] at this
    exact this.le
  choose R O hRD hO hRcov hRlcc using key
  have : Finite I := hIfin.to_subtype
  refine isLocallyChartCovered_of_cover (Zs := fun w : I => R w.1 w.2) (fun w => hRD _ _)
    (N₀ := g.baseMap ⁻¹' (⋃ w ∈ I, Set.range ((ofSaturation B).presentation.atlas.chart w)) ∩
      ⋂ w : I, O w.1 w.2)
    (Filter.inter_mem (g.baseMap.continuous.continuousAt.preimage_mem_nhds hInhds)
      (Filter.iInter_mem.mpr fun w => hO _ _)) ?_ fun w => hRlcc _ _
  rintro z ⟨hzD, hzg, hzO⟩
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hzg
  exact Set.mem_iUnion.mpr ⟨⟨w, hw⟩, hRcov w hw ⟨⟨hzD, hzw⟩, Set.mem_iInter.mp hzO ⟨w, hw⟩⟩⟩

section Global

variable {C S Pd P : SaturatedAtlasPresentation.{u, v, v} K}

theorem comp_comp_eq_of_numerators {Q : SaturatedAtlasPresentation.{u, v, v} K}
    (i : Pd ⟶ P) (g : P ⟶ Q)
    (ψ₁ ψ₂ : localizationFunctor.obj C ⟶ localizationFunctor.obj Pd) (σ : S ⟶ C)
    (x₁ x₂ : S ⟶ Pd)
    (h1 : localizationFunctor.map σ ≫ ψ₁ = localizationFunctor.map x₁)
    (h2 : localizationFunctor.map σ ≫ ψ₂ = localizationFunctor.map x₂)
    (heq : ψ₁ ≫ (localizationFunctor.map i ≫ localizationFunctor.map g) =
      ψ₂ ≫ (localizationFunctor.map i ≫ localizationFunctor.map g)) :
    (x₁ ≫ i) ≫ g = (x₂ ≫ i) ≫ g := by
  apply localizationFunctor_map_injective
  change localizationFunctor.map ((x₁ ≫ i) ≫ g) = localizationFunctor.map ((x₂ ≫ i) ≫ g)
  simp only [Functor.map_comp]
  rw [← h1, ← h2]
  simp only [Category.assoc, heq]

theorem eq_of_numerators_comp_mono (i : Pd ⟶ P) [Mono (localizationFunctor.map i)]
    (ψ₁ ψ₂ : localizationFunctor.obj C ⟶ localizationFunctor.obj Pd) (σ : S ⟶ C)
    (hσ : σ.IsQuasiIso) (x₁ x₂ : S ⟶ Pd)
    (h1 : localizationFunctor.map σ ≫ ψ₁ = localizationFunctor.map x₁)
    (h2 : localizationFunctor.map σ ≫ ψ₂ = localizationFunctor.map x₂)
    (hx : localizationFunctor.map (x₁ ≫ i) = localizationFunctor.map (x₂ ≫ i)) : ψ₁ = ψ₂ := by
  refine eq_of_numerators ψ₁ ψ₂ σ hσ x₁ x₂ h1 h2 ?_
  rw [Functor.map_comp, Functor.map_comp] at hx
  exact (cancel_mono (localizationFunctor.map i)).1 hx

end Global

/-- **Rigidity of étale maps over compact analytic domains.** Let `g` be an étale strong map of
saturations and `D` a compact Hausdorff analytic domain of its source. The restriction of `g` to
`D` is rigid. -/
theorem isRigidOn_domainInclusion_comp_etale (g : ofSaturation A ⟶ ofSaturation B)
    (hg : AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces (A := A) (B := B) g)
    (D : (ofSaturation A).AnalyticDomain) (hDc : IsCompact D.carrier) [T2Space D.carrier] :
    IsRigidOn (U := localizationFunctor.obj ((ofSaturation A).domain D))
      (X := localizationFunctor.obj (ofSaturation B))
      ((ofSaturation A).localizedDomainInclusion D ≫ localizationFunctor.map g) Set.univ := by
  classical
  -- a finite cover of `D` by rigid charts contained in `D`
  choose σ hσfin hσ N hN hNcov using fun y : D.carrier =>
    isLocallyChartCovered_isRigidChart g hg D y.2
  obtain ⟨t, ht⟩ := hDc.elim_nhds_subcover' (fun y hy => N ⟨y, hy⟩) (fun y hy => hN ⟨y, hy⟩)
  have hCfin : (⋃ y ∈ t, σ y).Finite := t.finite_toSet.biUnion fun y _ => hσfin y
  let Cs := hCfin.toFinset
  have hCmem : ∀ c ∈ Cs, IsRigidChart g c ∧
      Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆ D.carrier := by
    intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨y, -, hcy⟩ := Set.mem_iUnion₂.mp hc
    exact ⟨(hσ y c hcy).2.2, (hσ y c hcy).2.1⟩
  have hCcov : D.carrier ⊆ ⋃ c ∈ Cs, Set.range ((ofSaturation A).presentation.atlas.chart c) := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht hz)
    obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp (hNcov y ⟨hz, hzy⟩)
    exact Set.mem_iUnion₂.mpr ⟨c, (Set.Finite.mem_toFinset hCfin).mpr
      (Set.mem_iUnion₂.mpr ⟨y, hy, hc⟩), hzc⟩
  choose F δ hδ hrig using fun c : Cs => (hCmem c.1 c.2).1
  let dc : Cs → ((ofSaturation A).domain D).presentation.atlas.Index :=
    fun c => ⟨c.1, (hCmem c.1 c.2).2⟩
  let τf : (c : Cs) → (ofSaturation A).presentation.atlas.algebra c.1 →
      TestTriple ((ofSaturation A).domain D) :=
    fun c f => ⟨dc c, f, δ c / 2, half_pos (hδ c)⟩
  let τ0 : Cs → TestTriple ((ofSaturation A).domain D) := fun c => ⟨dc c, 0, 1, one_pos⟩
  let E : Finset (TestTriple ((ofSaturation A).domain D)) :=
    Finset.univ.biUnion fun c : Cs => (F c).image (τf c) ∪ {τ0 c}
  refine ⟨E, fun _ _ => Set.subset_univ _, fun V ψ ψ₁ ψ₂ _ _ _ heq hnear => ?_⟩
  obtain ⟨S, σ', hσ', x₀, x₁, x₂, h0, h1, h2, hn⟩ :=
    exists_strongNear_numerators (X := localizationFunctor.obj ((ofSaturation A).domain D))
      E ψ ψ₁ ψ₂ (fun τ hτ => (hnear τ hτ).1) (fun τ hτ => (hnear τ hτ).2)
  let incl := (ofSaturation A).domainInclusion D
  have hg' : (x₁ ≫ incl) ≫ g = (x₂ ≫ incl) ≫ g :=
    comp_comp_eq_of_numerators (C := presentationOf V) incl g ψ₁ ψ₂ σ' x₁ x₂ h1 h2 heq
  have hamb : ∀ τ ∈ E, StrongNear τ.ambient (x₀ ≫ incl) (x₁ ≫ incl) ∧
      StrongNear τ.ambient (x₀ ≫ incl) (x₂ ≫ incl) := fun τ hτ =>
    ⟨(strongNear_comp_domainInclusion_iff τ x₀ x₁).mpr (hn τ hτ).1,
      (strongNear_comp_domainInclusion_iff τ x₀ x₂).mpr (hn τ hτ).2⟩
  have hτ0 : ∀ c : Cs, τ0 c ∈ E := fun c =>
    Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_union_right _
      (Finset.mem_singleton_self _)⟩
  have hτf : ∀ (c : Cs) f, f ∈ F c → τf c f ∈ E := fun c f hf =>
    Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_union_left _
      (Finset.mem_image_of_mem _ hf)⟩
  have hx : localizationFunctor.map (x₁ ≫ incl) = localizationFunctor.map (x₂ ≫ incl) := by
    refine localizationFunctor_map_eq_of_local_eq (x₀ ≫ incl) (x₁ ≫ incl) (x₂ ≫ incl)
      D.carrier Cs (fun c hc => (hCmem c hc).2) hCcov (fun z => (x₀.baseMap z).property)
      (fun c hc => (hamb _ (hτ0 ⟨c, hc⟩)).1.1) (fun c hc => (hamb _ (hτ0 ⟨c, hc⟩)).2.1) ?_
    intro P c hc h₁ h₂ hPc
    have h₀ : (x₀ ≫ incl).baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
        Set.range ((ofSaturation A).presentation.atlas.chart c) := by
      rintro _ ⟨z, hz, rfl⟩
      exact hPc hz
    refine hrig ⟨c, hc⟩ S (x₁ ≫ incl) (x₂ ≫ incl) P h₁ h₂ hg' fun f hf p => ?_
    have hb₁ : p ((x₀ ≫ incl).pullback P c h₀ f - (x₁ ≫ incl).pullback P c h₁ f) ≤
        δ ⟨c, hc⟩ / 2 := (hamb _ (hτf ⟨c, hc⟩ f hf)).1.2.2 P ⟨h₀, h₁⟩ p
    have hb₂ : p ((x₀ ≫ incl).pullback P c h₀ f - (x₂ ≫ incl).pullback P c h₂ f) ≤
        δ ⟨c, hc⟩ / 2 := (hamb _ (hτf ⟨c, hc⟩ f hf)).2.2.2 P ⟨h₀, h₂⟩ p
    have htri := map_sub_le_add p.toMulRingSeminorm
      ((x₀ ≫ incl).pullback P c h₀ f - (x₂ ≫ incl).pullback P c h₂ f)
      ((x₀ ≫ incl).pullback P c h₀ f - (x₁ ≫ incl).pullback P c h₁ f)
    have e : ((x₀ ≫ incl).pullback P c h₀ f - (x₂ ≫ incl).pullback P c h₂ f) -
        ((x₀ ≫ incl).pullback P c h₀ f - (x₁ ≫ incl).pullback P c h₁ f) =
          (x₁ ≫ incl).pullback P c h₁ f - (x₂ ≫ incl).pullback P c h₂ f := by abel
    rw [e] at htri
    change p.toMulRingSeminorm _ ≤ _
    linarith
  have : Mono (localizationFunctor.map incl) :=
    inferInstanceAs (Mono ((ofSaturation A).localizedDomainInclusion D))
  exact eq_of_numerators_comp_mono (C := presentationOf V) incl ψ₁ ψ₂ σ' hσ' x₁ x₂ h1 h2 hx

end Langlands.Analytic.SaturatedAtlasPresentation
