import Langlands.Geometry.Analytic.FullRecognitionAllPiecesRestriction
import Langlands.Geometry.Analytic.FullRecognitionFiniteRightCancellationStatement

/-! # Cancellation into a finite affinoid neighborhood family -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {g' : StrongHom B.saturatedPresentation C.saturatedPresentation}

/-- Common-base finite cancellation supplies the otherwise missing finite
neighborhood of the first map. -/
theorem isFiniteAt_of_finiteOverRightCancellation
    (hcancel : FiniteOverRightCancellationStatement.{u, v, w} K)
    {y : A.space} (hg' : g'.IsFiniteAt (g.baseMap y))
    (hgg' : (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteAt y) : g.IsFiniteAt y := by
  let c := g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains
  obtain ⟨U₀, T₀, hU₀, hT₀, hxU₀, hfin'⟩ := hg'
  obtain ⟨V, T, hV, hT, hyV, hVU₀, hfin⟩ := hgg'.exists_small
    (g.baseMap.continuous.continuousAt.preimage_mem_nhds (hU₀.mem_nhds hxU₀))
  let T' := T ∩ T₀
  let U' := U₀ ∩ g'.baseMap ⁻¹' T'
  let V' := V ∩ c.baseMap ⁻¹' T'
  have hT' : IsOpen T' := hT.inter hT₀
  have hU' : IsOpen U' := hU₀.inter (hT'.preimage g'.baseMap.continuous)
  have hV' : IsOpen V' := hV.inter (hT'.preimage c.baseMap.continuous)
  have hyV' : y ∈ V' :=
    ⟨hyV, hfin.1 ⟨y, hyV, rfl⟩, hfin'.1 ⟨g.baseMap y, hxU₀, rfl⟩⟩
  have hVU : g.baseMap '' V' ⊆ U' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hVU₀ hp.1, hp.2⟩
  exact ⟨V', U', hV', hU', hyV', hcancel A B C g g' V' U' T' hV' hU' hT' hVU
    (hfin'.restrictTarget Set.inter_subset_right)
    (hfin.restrictTarget Set.inter_subset_left)⟩

/-- Cancellation of pointwise properties in the actual affinoid triangles
produces a finite family of pieces for the first map. The all-pieces upgrade
is deliberately separate. -/
theorem hasFinitePiecesAt_of_comp_of_isFiniteAt
    {Q Q' : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄,
      BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hpost : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (r : BoundedAlgHom K S T) (f : BoundedAlgHom K R S) (z : BanachSpectrum T),
      r.toAlgHom.toRingHom.Flat → Function.Surjective r →
      f.toAlgHom.toRingHom.FiniteType →
      Q f (BanachSpectrum.comap r.toBoundedRingHom z) → Q (r.comp f) z)
    (hpost' : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (r : BoundedAlgHom K S T) (f : BoundedAlgHom K R S) (z : BanachSpectrum T),
      r.toAlgHom.toRingHom.Flat → Function.Surjective r →
      f.toAlgHom.toRingHom.FiniteType →
      Q' f (BanachSpectrum.comap r.toBoundedRingHom z) → Q' (r.comp f) z)
    (hcancel : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (f : BoundedAlgHom K S T) (f' : BoundedAlgHom K R S) (z : BanachSpectrum T),
      f.toAlgHom.toRingHom.FiniteType → f'.toAlgHom.toRingHom.FiniteType →
      Q' f' (BanachSpectrum.comap f.toBoundedRingHom z) → Q (f.comp f') z → Q f z)
    {y : A.space} (hg : g.IsFiniteAt y)
    (hg' : g'.HasAllPiecesAt Q' (g.baseMap y))
    (hgg' : (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).HasAllPiecesAt Q y) :
    g.HasFinitePiecesAt Q y := by
  classical
  let c := g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains
  obtain ⟨V₀, T₀, hV₀, hT₀, hy₀, hfin₀, hQ₀⟩ := hgg'
  obtain ⟨U₂, T₂, hU₂, hT₂, hx₂, hfin₂, hQ₂⟩ := hg'
  obtain ⟨V₁, U₁, hV₁, hU₁, hy₁, hV₁₀, hfin₁⟩ :=
    hg.exists_small (hV₀.mem_nhds hy₀)
  obtain ⟨U₃, T₃, hU₃, hT₃, hx₃, hU₃₁, hU₃₂, hT₃₂, hfin₃⟩ :=
    hfin₂.exists_small hU₂ hT₂ hx₂ (hU₁.mem_nhds (hfin₁.1 ⟨y, hy₁, rfl⟩))
  let T := T₃ ∩ T₀
  let U := U₃ ∩ g'.baseMap ⁻¹' T
  let V := V₁ ∩ g.baseMap ⁻¹' U
  have hT : IsOpen T := hT₃.inter hT₀
  have hU : IsOpen U := hU₃.inter (hT.preimage g'.baseMap.continuous)
  have hV : IsOpen V := hV₁.inter (hU.preimage g.baseMap.continuous)
  have hxU : g.baseMap y ∈ U :=
    ⟨hx₃, hfin₃.1 ⟨g.baseMap y, hx₃, rfl⟩, hfin₀.1 ⟨y, hy₀, rfl⟩⟩
  have hyV : y ∈ V := ⟨hy₁, hxU⟩
  have hUU₁ : U ⊆ U₁ := Set.inter_subset_left.trans hU₃₁
  have hUU₂ : U ⊆ U₂ := Set.inter_subset_left.trans hU₃₂
  have hVV₀ : V ⊆ V₀ := Set.inter_subset_left.trans hV₁₀
  have hfinU : g'.IsFiniteOver U T := hfin₃.restrictTarget Set.inter_subset_left
  have hfinV : g.IsFiniteOver V U := hfin₁.restrictTarget hUU₁
  have hzT : c.baseMap y ∈ T := hfinU.1 ⟨g.baseMap y, hxU, rfl⟩
  obtain ⟨I, hI, hIT, hIN⟩ := C.atlas.exists_finite_recognized_nhds_subset
    (c.baseMap y) T (hT.mem_nhds hzT)
  let : Finite I := hI.to_subtype
  choose W hw hW hWfin using fun Z : I => hfinU.2 Z.1 (hIT Z.1 Z.2).2
  let J : Set B.atlas.saturatedAtlas.RecognizedSubset := Set.range W
  have hWU : ∀ Z : I, (W Z).locus ⊆ U :=
    fun Z => (hW Z).trans_subset Set.inter_subset_left
  have hxW : ∀ Z : I, g.baseMap y ∈ (W Z).locus := fun Z =>
    (hW Z).symm ▸ ⟨hxU, (hIT Z.1 Z.2).1⟩
  refine ⟨V, U, hV, hU, hyV, hfinV, J, Set.finite_range W, ?_, ?_, ?_⟩
  · rintro _ ⟨Z, rfl⟩
    exact ⟨hWU Z, hxW Z⟩
  · have hN : U ∩ g'.baseMap ⁻¹' (⋃ Z ∈ I, Z.locus) ∈ 𝓝 (g.baseMap y) :=
      Filter.inter_mem (hU.mem_nhds hxU)
        (g'.baseMap.continuous.continuousAt.preimage_mem_nhds hIN)
    refine Filter.mem_of_superset hN ?_
    rintro p ⟨hpU, hpI⟩
    obtain ⟨Z, hZI, hpZ⟩ := Set.mem_iUnion₂.1 hpI
    exact Set.mem_biUnion (⟨⟨Z, hZI⟩, rfl⟩ : W ⟨Z, hZI⟩ ∈ J)
      ((hW ⟨Z, hZI⟩).symm ▸ ⟨hpU, hpZ⟩)
  · rintro _ ⟨Z, rfl⟩ P h hP s hs
    obtain ⟨P₀, h₀, hP₀, hPfin⟩ := hfinV.2 (W Z) (hWU Z)
    have heq : P = P₀ := Subtype.ext (Subtype.ext (hP.trans hP₀.symm))
    subst heq
    have hc : c.baseMap '' Set.range P.chart ⊆ Set.range Z.1.chart := by
      rintro _ ⟨p, hp, rfl⟩
      exact hw Z ⟨g.baseMap p, h ⟨p, hp, rfl⟩, rfl⟩
    have hPc : P.locus = V ∩ c.baseMap ⁻¹' Z.1.locus := by
      rw [hP, hW Z]
      ext p
      constructor
      · rintro ⟨hpV, -, hpZ⟩
        exact ⟨hpV, hpZ⟩
      · rintro ⟨hpV, hpZ⟩
        exact ⟨hpV, hfinV.1 ⟨p, hpV, rfl⟩, hpZ⟩
    have hsW : (W Z).chart (BanachSpectrum.comap
        (g.fullRecognitionPairs.pullback P (W Z) h).toBoundedRingHom s) = g.baseMap y := by
      rw [← hs]
      exact g.fullRecognitionPairs.chart_comm P (W Z) h s
    have hQcomp := allPieces_restrict hpost hV hVV₀ Set.inter_subset_right hfin₀ hQ₀
      Z.1 (hIT Z.1 Z.2).2 (hIT Z.1 Z.2).1 P hc hPc s hs
    rw [fullRecognitionPairs_comp g g' P (W Z) Z.1 h (hw Z) hc] at hQcomp
    exact hcancel _ _ s hPfin.finite.finiteType (hWfin Z).finite.finiteType
      (allPieces_restrict hpost' hU hUU₂ (Set.inter_subset_left.trans hT₃₂)
        hfin₂ hQ₂ Z.1 (hIT Z.1 Z.2).2 (hIT Z.1 Z.2).1 (W Z) (hw Z) (hW Z) _ hsW)
      hQcomp

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
