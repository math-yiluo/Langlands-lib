import Langlands.Geometry.Analytic.LocalizedChartTransport
import Langlands.Geometry.Analytic.QuasiEtaleCompactCharts
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.SaturatedLocalizedFractions

/-! # The quasi-étale condition at a point of a saturated presentation -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A chart `i` of `S` is a quasi-étale chart for `ψ`: its affinoid domain is identified,
compatibly with `ψ`, with an affinoid domain of an analytic space étale over the target. -/
def IsQuasiEtaleChart (S : SaturatedAtlasPresentation.{u, v, v} K)
    {Z : LocalizedCategory.{u, v, v} (K := K)} (ψ : localizationFunctor.obj S ⟶ Z)
    (i : S.presentation.atlas.Index) : Prop :=
  ∃ (W : LocalizedCategory.{u, v, v} (K := K)) (w : W ⟶ Z)
    (j : localizationFunctor.obj (S.domain (S.chartDomain i)) ⟶ W),
    etale w ∧ IsAffinoidDomainEmbedding j ∧
      j ≫ w = S.localizedDomainInclusion (S.chartDomain i) ≫ ψ

/-- Berkovich's quasi-étale condition at a point `y` of `S` for an arrow `ψ` out of `S`:
finitely many quasi-étale charts of `S` have a union that is a neighbourhood of `y`. -/
def IsLocalizedQuasiEtaleAt (S : SaturatedAtlasPresentation.{u, v, v} K)
    {Z : LocalizedCategory.{u, v, v} (K := K)} (ψ : localizationFunctor.obj S ⟶ Z)
    (y : S.presentation.space) : Prop :=
  ∃ σ : Set (Set S.presentation.space), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 y ∧
    ∀ V ∈ σ, ∃ i : S.presentation.atlas.Index,
      Set.range (S.presentation.atlas.chart i) = V ∧ S.IsQuasiEtaleChart ψ i

/-- The quasi-étale condition at a point of a strong map is the pointwise condition for its
image. -/
theorem isQuasiEtaleAt_iff {A B : AffinoidAtlasPresentation.{u, v, v} K}
    (g : ofSaturation A ⟶ ofSaturation B) (y : A.space) :
    IsQuasiEtaleAt g y ↔
      (ofSaturation A).IsLocalizedQuasiEtaleAt (localizationFunctor.map g) y :=
  Iff.rfl

namespace IsLocalizedQuasiEtaleAt

variable {S : SaturatedAtlasPresentation.{u, v, v} K}
  {Z : LocalizedCategory.{u, v, v} (K := K)}

/-- The pointwise condition follows from a finite cover of a neighbourhood by sets each
covered by finitely many quasi-étale charts. -/
theorem of_cover {ψ : localizationFunctor.obj S ⟶ Z} {y : S.presentation.space}
    (τ : Set (Set S.presentation.space)) (hτ : τ.Finite) (hτn : ⋃₀ τ ∈ 𝓝 y)
    (h : ∀ U ∈ τ, ∃ σ : Set (Set S.presentation.space), σ.Finite ∧ U ⊆ ⋃₀ σ ∧
      ∀ V ∈ σ, ∃ i : S.presentation.atlas.Index,
        Set.range (S.presentation.atlas.chart i) = V ∧ S.IsQuasiEtaleChart ψ i) :
    S.IsLocalizedQuasiEtaleAt ψ y := by
  choose! σ hσf hσU hσg using h
  refine ⟨⋃ U ∈ τ, σ U, hτ.biUnion hσf, ?_, ?_⟩
  · refine Filter.mem_of_superset hτn ?_
    intro x hx
    obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.mp hx
    obtain ⟨V, hV, hxV⟩ := Set.mem_sUnion.mp (hσU U hU hxU)
    exact Set.mem_sUnion.mpr ⟨V, Set.mem_biUnion hU hV, hxV⟩
  · intro V hV
    obtain ⟨U, hU, hV⟩ := Set.mem_iUnion₂.mp hV
    exact hσg U hU V hV

/-- The pointwise condition is preserved by postcomposition with an arrow whose
postcomposition preserves étale arrows. -/
theorem comp {Z' : LocalizedCategory.{u, v, v} (K := K)} {ψ : localizationFunctor.obj S ⟶ Z}
    {y : S.presentation.space} (h : S.IsLocalizedQuasiEtaleAt ψ y) (χ : Z ⟶ Z')
    (hχ : ∀ (W : LocalizedCategory.{u, v, v} (K := K)) (w : W ⟶ Z), etale w → etale (w ≫ χ)) :
    S.IsLocalizedQuasiEtaleAt (ψ ≫ χ) y := by
  obtain ⟨σ, hσ, hn, hs⟩ := h
  refine ⟨σ, hσ, hn, fun V hV => ?_⟩
  obtain ⟨i, hi, W, w, j, hw, hj, hjw⟩ := hs V hV
  refine ⟨i, hi, W, w ≫ χ, j, hχ W w hw, hj, ?_⟩
  rw [← Category.assoc, hjw, Category.assoc]

/-- Postcomposition with an étale arrow. -/
theorem comp_etale {Z' : LocalizedCategory.{u, v, v} (K := K)}
    {ψ : localizationFunctor.obj S ⟶ Z} {y : S.presentation.space}
    (h : S.IsLocalizedQuasiEtaleAt ψ y) {χ : Z ⟶ Z'} (hχ : etale χ) :
    S.IsLocalizedQuasiEtaleAt (ψ ≫ χ) y :=
  h.comp χ fun _ _ hw => etale_comp hw hχ

/-- Postcomposition with an isomorphism. -/
theorem comp_iso {Z' : LocalizedCategory.{u, v, v} (K := K)}
    {ψ : localizationFunctor.obj S ⟶ Z} {y : S.presentation.space}
    (h : S.IsLocalizedQuasiEtaleAt ψ y) (χ : Z ⟶ Z') [IsIso χ] :
    S.IsLocalizedQuasiEtaleAt (ψ ≫ χ) y :=
  h.comp_etale (etale_of_isIso χ)

end IsLocalizedQuasiEtaleAt

/-- A quasi-étale chart of `S'` pulls back along an isomorphism `e : S ≅ S'` of analytic
spaces to every chart of `S` contained in its preimage. -/
theorem isQuasiEtaleChart_iso_comp {S S' : SaturatedAtlasPresentation.{u, v, v} K}
    {Z : LocalizedCategory.{u, v, v} (K := K)}
    (e : localizationFunctor.obj S ≅ localizationFunctor.obj S')
    (ψ : localizationFunctor.obj S' ⟶ Z) {i' : S'.presentation.atlas.Index}
    (h : S'.IsQuasiEtaleChart ψ i') (c : S.presentation.atlas.Index)
    (hc : Set.range (S.presentation.atlas.chart c) ⊆
      localizedSpaceFunctor.map e.hom ⁻¹' Set.range (S'.presentation.atlas.chart i')) :
    S.IsQuasiEtaleChart (e.hom ≫ ψ) c := by
  obtain ⟨W, w, j', hw, hj', hjw⟩ := h
  let D : S.AnalyticDomain := domainPreimage e.hom (S'.chartDomain i')
  let η : localizationFunctor.obj (S.domain D) ≅
      localizationFunctor.obj (S'.domain (S'.chartDomain i')) :=
    domainPreimageIso e (S'.chartDomain i')
  have hη : η.hom ≫ S'.localizedDomainInclusion (S'.chartDomain i') =
      S.localizedDomainInclusion D ≫ e.hom :=
    domainPreimageIso_hom_inclusion e (S'.chartDomain i')
  obtain ⟨m, hm⟩ := exists_localizedDomainLift D
    (S.localizedDomainInclusion (S.chartDomain c)) (by
      intro x
      have hx : localizedSpaceFunctor.map (S.localizedDomainInclusion (S.chartDomain c)) x =
          x.val :=
        S.localizedSpaceFunctor_map_localizedDomainInclusion (S.chartDomain c) x
      change localizedSpaceFunctor.map (S.localizedDomainInclusion (S.chartDomain c)) x ∈
        localizedSpaceFunctor.map e.hom ⁻¹' Set.range (S'.presentation.atlas.chart i')
      rw [hx]
      exact hc x.property)
  refine ⟨W, w, m ≫ η.hom ≫ j', hw,
    IsAffinoidDomainEmbedding.chart_comp S D (hj'.iso_comp η) c hc m hm, ?_⟩
  rw [Category.assoc, Category.assoc, hjw, reassoc_of% hη, reassoc_of% hm]

/-- Transport of the pointwise condition along an isomorphism of analytic spaces. -/
theorem IsLocalizedQuasiEtaleAt.of_iso {S S' : SaturatedAtlasPresentation.{u, v, v} K}
    {Z : LocalizedCategory.{u, v, v} (K := K)}
    (e : localizationFunctor.obj S ≅ localizationFunctor.obj S')
    {ψ : localizationFunctor.obj S' ⟶ Z} {y : S.presentation.space}
    (h : S'.IsLocalizedQuasiEtaleAt ψ (localizedSpaceFunctor.map e.hom y)) :
    S.IsLocalizedQuasiEtaleAt (e.hom ≫ ψ) y := by
  obtain ⟨σ', hσ', hn', hs'⟩ := h
  let F : S.presentation.space → S'.presentation.space := localizedSpaceFunctor.map e.hom
  have hF : Continuous F := (localizedSpaceFunctor.map e.hom).hom.continuous
  let H := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
  refine IsLocalizedQuasiEtaleAt.of_cover ((fun V => F ⁻¹' V) '' σ') (hσ'.image _) ?_ ?_
  · rw [Set.sUnion_image, ← Set.preimage_sUnion]
    exact hF.continuousAt.preimage_mem_nhds hn'
  · rintro _ ⟨V', hV', rfl⟩
    obtain ⟨i', rfl, hi'⟩ := hs' V' hV'
    let D : S.AnalyticDomain := domainPreimage e.hom (S'.chartDomain i')
    have hD : IsCompact D.carrier := by
      change IsCompact (H ⁻¹' Set.range (S'.presentation.atlas.chart i'))
      exact H.isCompact_preimage.mpr (S'.isCompactDomain_chartDomain i').1
    obtain ⟨σ, hσ, hσs, hcov⟩ := exists_finite_charts_of_isCompact S D hD
    refine ⟨σ, hσ, hcov, fun V hV => ?_⟩
    obtain ⟨c, rfl, hcD⟩ := hσs V hV
    exact ⟨c, rfl, isQuasiEtaleChart_iso_comp e ψ hi' c hcD⟩

/-- Pushforward of the pointwise condition along a strong domain embedding with open
image map. -/
theorem IsLocalizedQuasiEtaleAt.map_of_isDomainEmbedding
    {N Q : SaturatedAtlasPresentation.{u, v, v} K} {Z : LocalizedCategory.{u, v, v} (K := K)}
    (t : N ⟶ Q) (ht : AffinoidAtlasPresentation.StrongHom.IsDomainEmbedding t)
    (hto : IsOpenMap t.baseMap) {ψ : localizationFunctor.obj Q ⟶ Z}
    {x : N.presentation.space}
    (h : N.IsLocalizedQuasiEtaleAt (localizationFunctor.map t ≫ ψ) x) :
    Q.IsLocalizedQuasiEtaleAt ψ (t.baseMap x) := by
  obtain ⟨σ, hσ, hn, hs⟩ := h
  refine ⟨Set.image t.baseMap '' σ, hσ.image _, ?_, ?_⟩
  · rw [← Set.image_sUnion]
    exact hto.image_mem_nhds hn
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨c, rfl, W, w, j, hw, hj, hjw⟩ := hs V hV
    obtain ⟨d, hd, η, hη⟩ := exists_chart_iso_of_isDomainEmbedding t ht c
    refine ⟨d, hd, W, w, η.inv ≫ j, hw, hj.iso_comp η.symm, ?_⟩
    rw [Category.assoc, hjw, ← reassoc_of% hη, Iso.inv_hom_id_assoc]

/-- A quasi-étale arrow out of `S` satisfies the pointwise condition at every point. -/
theorem isLocalizedQuasiEtaleAt_of_quasiEtale {S : SaturatedAtlasPresentation.{u, v, v} K}
    {Z : LocalizedCategory.{u, v, v} (K := K)} {φ : localizationFunctor.obj S ⟶ Z}
    (hφ : quasiEtale φ) (y : S.presentation.space) : S.IsLocalizedQuasiEtaleAt φ y := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hφ
  let ex : localizationFunctor.obj (ofSaturation A) ≅ localizationFunctor.obj S :=
    Arrow.leftFunc.mapIso e
  let ey : localizationFunctor.obj (ofSaturation B) ≅ Z := Arrow.rightFunc.mapIso e
  have hw : ex.hom ≫ φ = localizationFunctor.map g ≫ ey.hom := e.hom.w
  have h1 : (ofSaturation A).IsLocalizedQuasiEtaleAt (localizationFunctor.map g ≫ ey.hom)
      (localizedSpaceFunctor.map ex.symm.hom y) :=
    ((isQuasiEtaleAt_iff g _).mp (hg _)).comp_iso ey.hom
  have h2 := IsLocalizedQuasiEtaleAt.of_iso ex.symm h1
  rw [← hw, Iso.symm_hom, Iso.inv_hom_id_assoc] at h2
  exact h2

/-- An arrow out of `S` satisfying the pointwise condition at every point is quasi-étale. -/
theorem quasiEtale_of_forall_isLocalizedQuasiEtaleAt
    {S : SaturatedAtlasPresentation.{u, v, v} K} {Z : LocalizedCategory.{u, v, v} (K := K)}
    (ψ : localizationFunctor.obj S ⟶ Z) (h : ∀ y, S.IsLocalizedQuasiEtaleAt ψ y) :
    quasiEtale ψ := by
  obtain ⟨φ, hφ⟩ := exists_localizedRightFraction (A := S) (B := presentationOf Z) ψ
  let N := φ.X'
  let eN : localizationFunctor.obj (ofSaturation N.presentation) ≅ localizationFunctor.obj S :=
    localizationFunctor.mapIso N.saturationIso ≪≫ localizedQuasiIso φ.s φ.hs
  let ε : localizationFunctor.obj (ofSaturation (presentationOf Z).presentation) ≅ Z :=
    localizationFunctor.mapIso (presentationOf Z).saturationIso
  let g : ofSaturation N.presentation ⟶ ofSaturation (presentationOf Z).presentation :=
    N.saturationIso.hom ≫ φ.f ≫ (presentationOf Z).saturationIso.inv
  have hg : localizationFunctor.map g = eN.hom ≫ ψ ≫ ε.inv := by
    rw [hφ]
    change _ = (localizationFunctor.map N.saturationIso.hom ≫ (localizedQuasiIso φ.s φ.hs).hom) ≫
      ((localizedQuasiIso φ.s φ.hs).inv ≫ localizationFunctor.map φ.f) ≫
        localizationFunctor.map (presentationOf Z).saturationIso.inv
    simp only [g, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  refine ⟨N.presentation, (presentationOf Z).presentation, g, fun y => ?_, ⟨?_⟩⟩
  · rw [isQuasiEtaleAt_iff, hg]
    exact IsLocalizedQuasiEtaleAt.of_iso eN ((h _).comp_iso ε.inv)
  · refine Arrow.isoMk eN ε ?_
    show eN.hom ≫ ψ = localizationFunctor.map g ≫ ε.hom
    rw [hg]
    simp

/-- An arrow is quasi-étale if and only if it satisfies the pointwise condition at every
point. -/
theorem quasiEtale_iff_forall_isLocalizedQuasiEtaleAt
    {S : SaturatedAtlasPresentation.{u, v, v} K} {Z : LocalizedCategory.{u, v, v} (K := K)}
    (ψ : localizationFunctor.obj S ⟶ Z) :
    quasiEtale ψ ↔ ∀ y, S.IsLocalizedQuasiEtaleAt ψ y :=
  ⟨isLocalizedQuasiEtaleAt_of_quasiEtale, quasiEtale_of_forall_isLocalizedQuasiEtaleAt ψ⟩

/-- A quasi-étale arrow followed by an étale arrow is quasi-étale. -/
theorem quasiEtale_comp_of_etale {X Y Z : LocalizedCategory.{u, v, v} (K := K)}
    {φ : X ⟶ Y} {χ : Y ⟶ Z} (hφ : quasiEtale φ) (hχ : etale χ) : quasiEtale (φ ≫ χ) :=
  quasiEtale_of_forall_isLocalizedQuasiEtaleAt (S := presentationOf X) (φ ≫ χ) fun y =>
    (isLocalizedQuasiEtaleAt_of_quasiEtale (S := presentationOf X) hφ y).comp_etale hχ

end Langlands.Analytic.SaturatedAtlasPresentation
