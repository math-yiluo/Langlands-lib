import Langlands.Geometry.Analytic.KeyLemma.LiftCharts
import Langlands.Geometry.Analytic.KeyLemma.RationalTestTransfer
import Langlands.Geometry.Analytic.QuasiEtaleActionLift.DomainTestTransfer
import Langlands.Geometry.Analytic.QuasiEtaleActionLift.LaurentEtaleLift
import Langlands.Geometry.Analytic.FullRecognitionAllPiecesRestriction

/-! # Local covers by charts with nearby lifts and rigidity -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every represented affinoid domain admits spectral test transfer. -/
theorem PresentedAffinoidAlgebra.Domain.hasSpectralTestTransfer
    {R : PresentedAffinoidAlgebra K} (U : Domain K R) :
    U.baseMap.HasSpectralTestTransfer :=
  U.hasSpectralTestTransfer_of_rational fun d F ε hε => by
    obtain ⟨E, δ, hδ, h⟩ := d.exists_transfer_tests F hε
    exact ⟨E, δ, hδ, fun _ => h⟩

namespace SaturatedAtlasPresentation

variable {A B : AffinoidAtlasPresentation.{u, v, v} K}

/-- The bounded pullback of a chart has spectral lifts for all reference
maps to test affinoids. This property can be transported between
different presentations of the same chart algebra. -/
def IsSpectralLiftChart (g : ofSaturation A ⟶ ofSaturation B)
    (c : (ofSaturation A).presentation.atlas.Index) : Prop :=
  ∃ (w : (ofSaturation B).presentation.atlas.Index)
    (hcw : g.baseMap '' Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆
      Set.range ((ofSaturation B).presentation.atlas.chart w)),
    (g.pullback c w hcw).HasSpectralLiftsOver Set.univ

theorem IsSpectralLiftChart.isLiftChart {g : ofSaturation A ⟶ ofSaturation B}
    {c : (ofSaturation A).presentation.atlas.Index} (h : IsSpectralLiftChart g c) :
    IsLiftChart g c := by
  obtain ⟨w, hcw, h⟩ := h
  refine ⟨w, hcw, fun F ε hε => ?_⟩
  obtain ⟨D, δ, hδ, hD⟩ := h F ε hε
  refine ⟨D, δ, hδ, fun S x y P hx hxg hy hSmall => ?_⟩
  apply hD (S.presentation.atlas.algebra P) (x.pullback P c hx) (y.pullback P w hy)
    (fun _ => Set.mem_univ _)
  intro r hr
  change BanachSpectrum.SpectralBound (y.pullback P w hy r -
    ((x.pullback P c hx).comp (g.pullback c w hcw)) r) δ
  rw [← comp_pullback_eq x g P c w hx hcw hxg]
  exact hSmall r hr

/-- On a chart inside a represented part of a finite affinoid piece, spectral
lifts on the piece and test transfer to the chart give nearby chart lifts. -/
theorem isSpectralLiftChart_of_spectralLiftsOver (g : ofSaturation A ⟶ ofSaturation B)
    (V : A.atlas.saturatedAtlas.RecognizedSubset) {R : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K R V.algebra) {L : Set (BanachSpectrum V.algebra)}
    (hLift : f.HasSpectralLiftsOver L) (c : (ofSaturation A).presentation.atlas.Index)
    (hcV : Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆ V.locus)
    (hcL : HasImageIn K (V.originalRestriction c hcV) L)
    (w : (ofSaturation B).presentation.atlas.Index)
    (hcw : g.baseMap '' Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆
      Set.range ((ofSaturation B).presentation.atlas.chart w))
    (ρ : BoundedAlgHom K R ((ofSaturation B).presentation.atlas.algebra w))
    (hρ : Function.Surjective ρ)
    (hcompat : (V.originalRestriction c hcV).comp f = (g.pullback c w hcw).comp ρ) :
    IsSpectralLiftChart g c := by
  classical
  let res := V.originalRestriction c hcV
  have hTransfer : res.HasSpectralTestTransfer := (V.originalDomain c hcV).hasSpectralTestTransfer
  refine ⟨w, hcw, fun F ε hε => ?_⟩
  obtain ⟨E, η, hη, hE⟩ := hTransfer F ε hε
  obtain ⟨D, δ, hδ, hD⟩ := hLift E η hη
  refine ⟨D.image ρ, δ, hδ, fun C a b _ hSmall => ?_⟩
  let g₀ := g.pullback c w hcw
  have hReference : HasImageIn K (a.comp res) L := fun p =>
    hcL (BanachSpectrum.comap a.toBoundedRingHom p)
  have hBase : (a.comp res).comp f = (a.comp g₀).comp ρ := calc
    _ = a.comp (res.comp f) := rfl
    _ = a.comp (g₀.comp ρ) := congrArg (fun m => a.comp m) hcompat
    _ = _ := rfl
  have hInput (r : R) (hr : r ∈ D) :
      BanachSpectrum.SpectralBound ((b.comp ρ) r - (a.comp res) (f r)) δ := by
    change BanachSpectrum.SpectralBound ((b.comp ρ) r - ((a.comp res).comp f) r) δ
    rw [hBase]
    exact hSmall (ρ r) (Finset.mem_image_of_mem ρ hr)
  obtain ⟨a₀, ha₀, hClose⟩ := hD C (a.comp res) (b.comp ρ) hReference hInput
  obtain ⟨a', ha', hNear⟩ := hE C a a₀ hClose
  refine ⟨a', ?_, hNear⟩
  have hOver : (a'.comp g₀).comp ρ = b.comp ρ := calc
    _ = a'.comp (g₀.comp ρ) := rfl
    _ = a'.comp (res.comp f) := congrArg (fun m => a'.comp m) hcompat.symm
    _ = a₀.comp f := congrArg (fun m => m.comp f) ha'
    _ = _ := ha₀
  apply BoundedAlgHom.ext
  intro t
  obtain ⟨r, rfl⟩ := hρ t
  exact congrArg (fun m : BoundedAlgHom K R C => m r) hOver

private theorem surjective_originalRestriction_of_locus_eq
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (w : (ofSaturation B).presentation.atlas.Index)
    (hW : W.locus = Set.range ((ofSaturation B).presentation.atlas.chart w)) :
    Function.Surjective (W.originalRestriction w hW.symm.subset) := by
  let U := W.originalDomain w hW.symm.subset
  have hU : U.locus = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    change W.chart p ∈ Set.range ((ofSaturation B).presentation.atlas.chart w)
    rw [← hW, ← W.range_chart]
    exact Set.mem_range_self p
  obtain ⟨inv, hinv, _⟩ := U.represents.2.2 W.algebra (BoundedAlgHom.id K W.algebra)
    (fun p => hU.symm ▸ Set.mem_univ _)
  have hEq : U.baseMap.comp inv = BoundedAlgHom.id K U.algebra := by
    apply U.represents.hom_ext
    change U.baseMap.comp (inv.comp U.baseMap) = U.baseMap
    rw [hinv, BoundedAlgHom.comp_id]
  exact fun t => ⟨inv t, congrArg (fun m : BoundedAlgHom K U.algebra U.algebra => m t) hEq⟩

/-- Each point of an analytic domain in the source of an étale strong map has
a local chart cover on which nearby lifts exist and are rigid. -/
theorem isLocallyChartCovered_isSpectralLiftChart_and_isRigidChart
    (g : ofSaturation A ⟶ ofSaturation B)
    (hg : AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces (A := A) (B := B) g)
    (D : (ofSaturation A).AnalyticDomain) {y : (ofSaturation A).presentation.space}
    (hy : y ∈ D.carrier) :
    (ofSaturation A).IsLocallyChartCovered (fun c => IsSpectralLiftChart g c ∧ IsRigidChart g c)
      D.carrier y := by
  classical
  obtain ⟨V₀, -, hyV₀, hV₀⟩ := hg y
  have hJoint := AffinoidAtlasPresentation.StrongHom.hasAllPiecesAt_isEtaleAtPoint_iff.mpr
    (hV₀ y hyV₀)
  obtain ⟨Vy, Uy, hVy, hUy, hyVy, hfinite, hpieces⟩ := hJoint
  have hgyU : g.baseMap y ∈ Uy := hfinite.1 ⟨y, hyVy, rfl⟩
  obtain ⟨I, hIfin, hImem, hInhds⟩ :=
    IndexedAffinoidAtlas.HasAllLocalDomains.exists_finite_chart_nhds_subset
      (ofSaturation B).presentation.atlas (ofSaturation B).hasAllLocalDomains (g.baseMap y) Uy
      (hUy.mem_nhds hgyU)
  have key : ∀ w ∈ I, ∃ (R O : Set (ofSaturation A).presentation.space), R ⊆ D.carrier ∧
      O ∈ 𝓝 y ∧
      D.carrier ∩ g.baseMap ⁻¹' Set.range ((ofSaturation B).presentation.atlas.chart w) ∩ O ⊆
        R ∧ (ofSaturation A).IsLocallyChartCovered
          (fun c => IsSpectralLiftChart g c ∧ IsRigidChart g c) R y := by
    intro w hw
    let W := B.atlas.saturatedAtlas.originalRecognitionIndex w
    have hWlocus : W.locus = Set.range ((ofSaturation B).presentation.atlas.chart w) :=
      W.range_chart.symm.trans (B.atlas.saturatedAtlas.recognitionAtlas_original_range w)
    have hWU : W.locus ⊆ Uy := hWlocus ▸ (hImem w hw).2
    have hgyW : g.baseMap y ∈ W.locus := hWlocus ▸ (hImem w hw).1
    obtain ⟨V, hVW, hVeq, hfin⟩ := hfinite.2 W hWU
    have hyV : y ∈ V.locus := by
      rw [hVeq]
      exact ⟨hyVy, hgyW⟩
    let s := V.coordinates ⟨y, hyV⟩
    have hs : V.chart s = y := by
      change (V.coordinates.symm s).val = y
      rw [V.coordinates.symm_apply_apply]
    let f := g.fullRecognitionPairs.pullback V W hVW
    have hEtale : f.IsEtaleAtPoint s := hpieces W hWU hgyW V hVW hVeq s hs
    obtain ⟨d, hd, hLift⟩ := f.exists_hasSpectralLiftsOver_of_isEtaleAtPoint hfin s hEtale
    have hInt : s ∈ interior d.locus := mem_interior_iff_mem_nhds.mpr hd
    have hun := hEtale.2
    unfold BoundedAlgHom.IsUnramifiedAtPoint at hun
    obtain ⟨e, he, hes⟩ := SetLike.not_le_iff_exists.mp hun
    have hes0 : 0 < s e := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hes)
    have hval : Continuous fun z : V.locus => V.coordinates z e :=
      (BanachSpectrum.evaluation e).continuous.comp V.coordinates.continuous
    have hOpen : IsOpen {z : V.locus | V.coordinates z ∈ interior d.locus ∧
        s e / 2 < V.coordinates z e} :=
      (isOpen_interior.preimage V.coordinates.continuous).inter (isOpen_lt continuous_const hval)
    obtain ⟨O₁, hO₁, hO₁eq⟩ := isOpen_induced_iff.mp hOpen
    have hyO₁ : y ∈ O₁ := by
      have : (⟨y, hyV⟩ : V.locus) ∈ Subtype.val ⁻¹' O₁ := by
        rw [hO₁eq]
        exact ⟨hInt, half_lt_self hes0⟩
      exact this
    have hOnhds : Vy ∩ O₁ ∈ 𝓝 y := (hVy.inter hO₁).mem_nhds ⟨hyVy, hyO₁⟩
    refine ⟨D.carrier ∩ g.baseMap ⁻¹' Set.range ((ofSaturation B).presentation.atlas.chart w) ∩
      (Vy ∩ O₁), Vy ∩ O₁, fun z hz => hz.1.1, hOnhds, fun z hz => hz, ?_⟩
    refine (((isLocallyChartCovered_analyticDomain D hy).inter
      (isLocallyChartCovered_preimage g w (hImem w hw).1)).inter
        (isLocallyChartCovered_of_mem_nhds hOnhds)).of_subset_pred fun c hc => ?_
    have hcV : Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆ V.locus := by
      intro z hz
      rw [hVeq]
      exact ⟨(hc hz).2.1, hWlocus ▸ (hc hz).1.2⟩
    have hcw : g.baseMap '' Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆
        Set.range ((ofSaturation B).presentation.atlas.chart w) := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hc hz).1.2
    have hcNear (z : (ofSaturation A).presentation.space)
        (hz : z ∈ Set.range ((ofSaturation A).presentation.atlas.chart c)) :
        V.coordinates ⟨z, hcV hz⟩ ∈ d.locus ∧ s e / 2 ≤ V.coordinates ⟨z, hcV hz⟩ e := by
      have hz' : (⟨z, hcV hz⟩ : V.locus) ∈ Subtype.val ⁻¹' O₁ := (hc hz).2.2
      rw [hO₁eq] at hz'
      exact ⟨interior_subset hz'.1, hz'.2.le⟩
    have hcL : HasImageIn K (V.originalRestriction c hcV) d.locus := by
      intro p
      rw [V.comap_originalRestriction c hcV p]
      exact (hcNear _ (Set.mem_range_self p)).1
    have hcompat := AffinoidAtlasPresentation.StrongHom.originalRestriction_comp_fullRecognitionPairs
      g V W hVW c hcV w hWlocus.symm.subset hcw
    refine ⟨isSpectralLiftChart_of_spectralLiftsOver g V f hLift c hcV hcL w hcw
      (W.originalRestriction w hWlocus.symm.subset)
      (surjective_originalRestriction_of_locus_eq W w hWlocus) hcompat, ?_⟩
    exact isRigidChart_of_unramified g V f hfin.finite.finiteType e he (half_pos hes0) c hcV w
      hcw (W.originalRestriction w hWlocus.symm.subset) hcompat fun z hz => (hcNear z hz).2
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

theorem isLocallyChartCovered_isLiftChart_and_isRigidChart (g : ofSaturation A ⟶ ofSaturation B)
    (hg : AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces (A := A) (B := B) g)
    (D : (ofSaturation A).AnalyticDomain) {y : (ofSaturation A).presentation.space}
    (hy : y ∈ D.carrier) :
    (ofSaturation A).IsLocallyChartCovered (fun c => IsLiftChart g c ∧ IsRigidChart g c)
      D.carrier y := by
  obtain ⟨σ, hσ, hm, N, hN, hcov⟩ := isLocallyChartCovered_isSpectralLiftChart_and_isRigidChart g hg D hy
  refine ⟨σ, hσ, fun c hc => ?_, N, hN, hcov⟩
  obtain ⟨hyc, hcD, hlift, hrigid⟩ := hm c hc
  exact ⟨hyc, hcD, hlift.isLiftChart, hrigid⟩

end SaturatedAtlasPresentation

end Langlands.Analytic
