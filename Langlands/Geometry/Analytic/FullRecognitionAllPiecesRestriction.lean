import Langlands.Geometry.Analytic.FullRecognitionEtaleComposition

/-! # Shrinking and combining properties over all recognized pieces -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- Transfer an all-pieces certificate to a smaller open source and smaller
target. Each supplied recognized new preimage is a clopen part of the old
preimage. -/
theorem allPieces_restrict
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hpost : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (r : BoundedAlgHom K S T) (f : BoundedAlgHom K R S) (z : BanachSpectrum T),
      r.toAlgHom.toRingHom.Flat → Function.Surjective r →
      f.toAlgHom.toRingHom.FiniteType →
      Q f (BanachSpectrum.comap r.toBoundedRingHom z) → Q (r.comp f) z)
    {y : A.space} {V₀ V : Set A.space} {U₀ U : Set B.space}
    (hV : IsOpen V) (hVV₀ : V ⊆ V₀) (hUU₀ : U ⊆ U₀)
    (hfin₀ : g.IsFiniteOver V₀ U₀)
    (hQ₀ : ∀ W : B.atlas.saturatedAtlas.RecognizedSubset,
      W.locus ⊆ U₀ → g.baseMap y ∈ W.locus →
      ∀ (P : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
        P.locus = V₀ ∩ g.baseMap ⁻¹' W.locus →
        ∀ s : BanachSpectrum P.algebra, P.chart s = y →
          Q (g.fullRecognitionPairs.pullback P W h) s) :
    ∀ W : B.atlas.saturatedAtlas.RecognizedSubset,
      W.locus ⊆ U → g.baseMap y ∈ W.locus →
      ∀ (P : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
        P.locus = V ∩ g.baseMap ⁻¹' W.locus →
        ∀ s : BanachSpectrum P.algebra, P.chart s = y →
          Q (g.fullRecognitionPairs.pullback P W h) s := by
  intro W hWU hxW P h hP s hs
  obtain ⟨P₀, h₀, hP₀, hfinP₀⟩ := hfin₀.2 W (hWU.trans hUU₀)
  have hPP₀ : P.locus = P₀.locus ∩ V := by
    rw [hP, hP₀]
    ext p
    constructor
    · rintro ⟨hpV, hpW⟩
      exact ⟨⟨hVV₀ hpV, hpW⟩, hpV⟩
    · rintro ⟨⟨-, hpW⟩, hpV⟩
      exact ⟨hpV, hpW⟩
  have hsub : P.locus ⊆ P₀.locus := hPP₀.trans_subset Set.inter_subset_left
  have hcl := P.isClopen_chart_preimage_of_eq_inter P₀ hV hPP₀
  obtain ⟨hrflat, hrsurj⟩ := P.restriction_flat_and_surjective P₀ hsub hcl
  have hPr : Set.range P.chart ⊆ Set.range P₀.chart := by
    rw [P.range_chart, P₀.range_chart]
    exact hsub
  have hcomm := g.fullRecognitionPairs.restriction_comm P P₀ W W hPr
    (Set.Subset.refl _) h h₀
  rw [B.fullRecognitionPresentation.atlas.restriction_id W (Set.Subset.refl _),
    BoundedAlgHom.comp_id] at hcomm
  rw [← hcomm]
  exact hpost _ _ s hrflat hrsurj hfinP₀.finite.finiteType
    (hQ₀ W (hWU.trans hUU₀) hxW P₀ h₀ hP₀ _
      ((P.chart_restriction P₀ hsub s).trans hs))

/-- A property preserved by flat surjective restrictions can be retained
while shrinking the finite neighborhood into any prescribed neighborhood. -/
theorem HasAllPiecesAt.exists_small
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hpost : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (r : BoundedAlgHom K S T) (f : BoundedAlgHom K R S) (z : BanachSpectrum T),
      r.toAlgHom.toRingHom.Flat → Function.Surjective r →
      f.toAlgHom.toRingHom.FiniteType →
      Q f (BanachSpectrum.comap r.toBoundedRingHom z) → Q (r.comp f) z)
    {y : A.space} (hg : g.HasAllPiecesAt Q y) {O : Set A.space} (hO : O ∈ 𝓝 y) :
    ∃ (V : Set A.space) (U : Set B.space), IsOpen V ∧ IsOpen U ∧ y ∈ V ∧ V ⊆ O ∧
      g.IsFiniteOver V U ∧
      ∀ W : B.atlas.saturatedAtlas.RecognizedSubset,
        W.locus ⊆ U → g.baseMap y ∈ W.locus →
        ∀ (P : A.atlas.saturatedAtlas.RecognizedSubset)
          (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
          P.locus = V ∩ g.baseMap ⁻¹' W.locus →
          ∀ s : BanachSpectrum P.algebra, P.chart s = y →
            Q (g.fullRecognitionPairs.pullback P W h) s := by
  obtain ⟨V₀, U₀, hV₀, hU₀, hy, hfin₀, hQ₀⟩ := hg
  obtain ⟨V, U, hV, hU, hyV, hVO, hVV₀, hUU₀, hfin⟩ :=
    hfin₀.exists_small hV₀ hU₀ hy hO
  exact ⟨V, U, hV, hU, hyV, hVO, hfin,
    allPieces_restrict hpost hV hVV₀ hUU₀ hfin₀ hQ₀⟩

/-- Properties holding over all pieces can be combined on one finite
neighborhood when both survive clopen source restrictions. -/
theorem HasAllPiecesAt.and
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
    {y : A.space} (hg : g.HasAllPiecesAt Q y) (hg' : g.HasAllPiecesAt Q' y) :
    g.HasAllPiecesAt (fun _ _ f s => Q f s ∧ Q' f s) y := by
  obtain ⟨V₂, U₂, hV₂, hU₂, hy₂, hfin₂, hQ₂⟩ := hg'
  obtain ⟨V₁, U₁, hV₁, hU₁, hy₁, hV₁₂, hfin₁, hQ₁⟩ :=
    hg.exists_small hpost (hV₂.mem_nhds hy₂)
  let U := U₁ ∩ U₂
  let V := V₁ ∩ g.baseMap ⁻¹' U
  have hV : IsOpen V := hV₁.inter ((hU₁.inter hU₂).preimage g.baseMap.continuous)
  have hyV : y ∈ V :=
    ⟨hy₁, hfin₁.1 ⟨y, hy₁, rfl⟩, hfin₂.1 ⟨y, hy₂, rfl⟩⟩
  have hV₁sub : V ⊆ V₁ := Set.inter_subset_left
  have hV₂sub : V ⊆ V₂ := hV₁sub.trans hV₁₂
  have hfin : g.IsFiniteOver V U := hfin₁.restrictTarget Set.inter_subset_left
  refine ⟨V, U, hV, hU₁.inter hU₂, hyV, hfin, ?_⟩
  intro W hWU hxW P h hP s hs
  exact ⟨allPieces_restrict hpost hV hV₁sub Set.inter_subset_left
      hfin₁ hQ₁ W hWU hxW P h hP s hs,
    allPieces_restrict hpost' hV hV₂sub Set.inter_subset_right
      hfin₂ hQ₂ W hWU hxW P h hP s hs⟩

/-- A pointwise implication preserves all-pieces certificates. -/
theorem HasAllPiecesAt.mono
    {Q Q' : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄,
      BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hQQ' : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄ (f : BoundedAlgHom K R S) (s),
      Q f s → Q' f s)
    {y : A.space} (hg : g.HasAllPiecesAt Q y) : g.HasAllPiecesAt Q' y := by
  obtain ⟨V, U, hV, hU, hy, hfin, hQ⟩ := hg
  exact ⟨V, U, hV, hU, hy, hfin,
    fun W hW hx P h hP s hs => hQQ' _ _ (hQ W hW hx P h hP s hs)⟩

/-- Separate flat and unramified all-pieces witnesses are equivalent to one
joint pointwise-étale witness. -/
theorem hasAllPiecesAt_isEtaleAtPoint_iff {y : A.space} :
    g.HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y ↔
      g.IsUnramifiedAtAllPieces y ∧ g.IsFlatAtAllPieces y := by
  constructor
  · intro hg
    exact ⟨hg.mono (fun _ _ _ _ h => h.2), hg.mono (fun _ _ _ _ h => h.1)⟩
  · rintro ⟨hunr, hflat⟩
    exact hflat.and
      (fun _ _ _ r f z hr _ _ hf => (r.isFlatAtPoint_of_flat hr z).comp hf)
      (fun _ _ _ r f z _ hrs hft hf =>
        BoundedAlgHom.IsUnramifiedAtPoint.comp
          (RingHom.Finite.of_surjective _ hrs).finiteType hft
          (r.isUnramifiedAtPoint_of_formallyUnramified
            (RingHom.FormallyUnramified.of_surjective hrs) z) hf)
      hunr

/-- The joint-witness equivalence, with every presentation and point
quantified, for use as an internal reviewed interface. -/
def AllPiecesJointEtaleStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B : AffinoidAtlasPresentation.{u, v, w} K)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) (y : A.space),
    g.HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y ↔
      g.IsUnramifiedAtAllPieces y ∧ g.IsFlatAtAllPieces y

theorem allPiecesJointEtale : AllPiecesJointEtaleStatement.{u, v, w} K := by
  intro A B g y
  exact hasAllPiecesAt_isEtaleAtPoint_iff

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
