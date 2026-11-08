import Langlands.Geometry.Analytic.ClopenPieceLocalization

/-! # Flat, unramified and étale morphisms over all affinoid pieces, and their composition -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Berkovich's Proposition 3.2.3(b) for a pointwise property `Q` of finite
affinoid maps: open neighborhoods `V` of `y` and `U` of its image between which
`g` induces a finite morphism, such that the induced finite affinoid map over
every recognized affinoid subset of `U` containing the image point has the
property `Q` at `y`. -/
def HasAllPiecesAt
    (Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) (y : A.space) : Prop :=
  ∃ (V : Set A.space) (U : Set B.space), IsOpen V ∧ IsOpen U ∧ y ∈ V ∧ g.IsFiniteOver V U ∧
    ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ U → g.baseMap y ∈ W.locus →
      ∀ (V' : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus →
          ∀ s : BanachSpectrum V'.algebra, V'.chart s = y →
            Q (g.fullRecognitionPairs.pullback V' W h) s

/-- Flatness at a point in the form of Definition 3.2.5 with Proposition
3.2.3(b). -/
def IsFlatAtAllPieces (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) : Prop :=
  g.HasAllPiecesAt (fun _ _ f s => f.IsFlatAtPoint s) y

/-- Unramifiedness at a point over all affinoid pieces. -/
def IsUnramifiedAtAllPieces (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) : Prop :=
  g.HasAllPiecesAt (fun _ _ f s => f.IsUnramifiedAtPoint s) y

/-- Étaleness at a point over all affinoid pieces: an open neighborhood of
unramified and flat points. -/
def IsEtaleAtAllPieces (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) : Prop :=
  ∃ V : Set A.space, IsOpen V ∧ y ∈ V ∧
    ∀ y' ∈ V, g.IsUnramifiedAtAllPieces y' ∧ g.IsFlatAtAllPieces y'

/-- Étale morphisms over all affinoid pieces. -/
def IsEtaleAllPieces (g : StrongHom A.saturatedPresentation B.saturatedPresentation) : Prop :=
  ∀ y, g.IsEtaleAtAllPieces y

section Basic

variable {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- Property (b) implies property (a): the neighborhood basis of recognized
subsets supplies the finite family. -/
theorem HasAllPiecesAt.hasFinitePiecesAt
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    {y : A.space} (hg : g.HasAllPiecesAt Q y) : g.HasFinitePiecesAt Q y := by
  obtain ⟨V, U, hV, hU, hy, hfin, hQ⟩ := hg
  have hUy : U ∈ 𝓝 (g.baseMap y) := hU.mem_nhds (hfin.1 ⟨y, hy, rfl⟩)
  obtain ⟨I, hI, hIU, hIN⟩ :=
    B.atlas.exists_finite_recognized_nhds_subset (g.baseMap y) U hUy
  exact ⟨V, U, hV, hU, hy, hfin, I, hI, fun W hW => ⟨(hIU W hW).2, (hIU W hW).1⟩, hIN,
    fun W hW V' h hV' s hs => hQ W (hIU W hW).2 (hIU W hW).1 V' h hV' s hs⟩

theorem IsFlatAtAllPieces.isFlatAt {y : A.space} (hg : g.IsFlatAtAllPieces y) :
    g.IsFlatAt y :=
  HasAllPiecesAt.hasFinitePiecesAt hg

theorem IsUnramifiedAtAllPieces.isUnramifiedAt {y : A.space}
    (hg : g.IsUnramifiedAtAllPieces y) : g.IsUnramifiedAt y :=
  HasAllPiecesAt.hasFinitePiecesAt hg

theorem IsEtaleAtAllPieces.isEtaleAt {y : A.space} (hg : g.IsEtaleAtAllPieces y) :
    g.IsEtaleAt y := by
  obtain ⟨V, hV, hy, hV'⟩ := hg
  exact ⟨V, hV, hy, fun y' hy' => ⟨(hV' y' hy').1.isUnramifiedAt, (hV' y' hy').2.isFlatAt⟩⟩

theorem IsEtaleAllPieces.isEtale (hg : g.IsEtaleAllPieces) : g.IsEtale :=
  isEtale_iff_forall_isEtaleAt.2 fun y => (hg y).isEtaleAt

/-- A finite morphism between open sets whose pieces all have `Q` at every
point has `Q` over all pieces at every point of the source. -/
theorem hasAllPiecesAt_of_isFiniteOver
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    {V : Set A.space} {U : Set B.space} (hV : IsOpen V) (hU : IsOpen U)
    (hfin : g.IsFiniteOver V U)
    (hQ : ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ U →
      ∀ (V' : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus →
          ∀ s : BanachSpectrum V'.algebra, Q (g.fullRecognitionPairs.pullback V' W h) s)
    {y : A.space} (hy : y ∈ V) : g.HasAllPiecesAt Q y :=
  ⟨V, U, hV, hU, hy, hfin, fun W hW _ V' h hV' s _ => hQ W hW V' h hV' s⟩

/-- Locally finite étale morphisms are étale over all pieces at the point. -/
theorem IsLocallyFiniteEtaleAt.isEtaleAtAllPieces {y : A.space}
    (hg : g.IsLocallyFiniteEtaleAt y) : g.IsEtaleAtAllPieces y := by
  obtain ⟨V, U, hV, hU, hy, hfe⟩ := hg
  have hpieces : ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ U →
      ∀ (V' : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus →
          ∀ s : BanachSpectrum V'.algebra,
            (g.fullRecognitionPairs.pullback V' W h).IsEtaleAtPoint s := by
    intro W hW V' h hV' s
    obtain ⟨V'', h'', hV'', -, hetale⟩ := hfe.2 W hW
    have hVV : V' = V'' := Subtype.ext (Subtype.ext (hV'.trans hV''.symm))
    subst hVV
    exact hetale.isEtaleAtPoint s
  refine ⟨V, hV, hy, fun y' hy' => ⟨?_, ?_⟩⟩
  · exact hasAllPiecesAt_of_isFiniteOver hV hU hfe.isFiniteOver
      (fun W hW V' h hV' s => (hpieces W hW V' h hV' s).2) hy'
  · exact hasAllPiecesAt_of_isFiniteOver hV hU hfe.isFiniteOver
      (fun W hW V' h hV' s => (hpieces W hW V' h hV' s).1) hy'

theorem IsFiniteEtale.isEtaleAllPieces (hg : g.IsFiniteEtale) : g.IsEtaleAllPieces :=
  fun y => IsLocallyFiniteEtaleAt.isEtaleAtAllPieces
    ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, Set.mem_univ y, hg⟩

end Basic

section Composition

variable {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {g' : StrongHom B.saturatedPresentation C.saturatedPresentation}

/-- Composition of a pointwise property over all pieces, for a property that
composes along maps of finite type and holds for flat surjective maps. The
source neighborhood of the second map is shrunk into the target neighborhood
of the first by Lemma 3.1.2. The new pieces of the second map are clopen
pieces of its old pieces, reached by flat surjective restrictions. -/
theorem HasAllPiecesAt.comp
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hcomp : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄ (f : BoundedAlgHom K S T)
      (f' : BoundedAlgHom K R S) (z : BanachSpectrum T),
      f.toAlgHom.toRingHom.FiniteType → f'.toAlgHom.toRingHom.FiniteType → Q f z →
        Q f' (BanachSpectrum.comap f.toBoundedRingHom z) → Q (f.comp f') z)
    (hres : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄ (r : BoundedAlgHom K R S),
      r.toAlgHom.toRingHom.Flat → Function.Surjective r → ∀ z, Q r z)
    {y : A.space} (hg : g.HasAllPiecesAt Q y) (hg' : g'.HasAllPiecesAt Q (g.baseMap y)) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).HasAllPiecesAt Q y := by
  obtain ⟨V, U, hV, hU, hy, hfin, hQg⟩ := hg
  obtain ⟨U₂, T₂, hU₂, hT₂, hx, hfin', hQg'⟩ := hg'
  have hxU : g.baseMap y ∈ U := hfin.1 ⟨y, hy, rfl⟩
  obtain ⟨U₃, T₃, hU₃, hT₃, hx₃, hU₃U, hU₃U₂, hT₃T₂, hfin₃⟩ :=
    hfin'.exists_small hU₂ hT₂ hx (hU.mem_nhds hxU)
  have hfinR := hfin.restrictTarget hU₃U
  refine ⟨V ∩ g.baseMap ⁻¹' U₃, T₃, hV.inter (hU₃.preimage g.baseMap.continuous), hT₃,
    ⟨hy, hx₃⟩, hfinR.comp hfin₃, ?_⟩
  intro Z hZT hzZ V'' h'' hV'' s hs
  have hzZ' : g'.baseMap (g.baseMap y) ∈ Z.locus := hzZ
  -- the new piece of `g'` over `Z`
  obtain ⟨Q₃, hQ₃h, hQ₃, hQ₃fin⟩ := hfin₃.2 Z hZT
  -- the old piece of `g'` over `Z`
  obtain ⟨Q₂, hQ₂h, hQ₂, hQ₂fin⟩ := hfin'.2 Z (hZT.trans hT₃T₂)
  have hQ₃₂ : Q₃.locus = Q₂.locus ∩ U₃ := by
    rw [hQ₃, hQ₂]
    ext p
    constructor
    · rintro ⟨hp₃, hpZ⟩
      exact ⟨⟨hU₃U₂ hp₃, hpZ⟩, hp₃⟩
    · rintro ⟨⟨-, hpZ⟩, hp₃⟩
      exact ⟨hp₃, hpZ⟩
  have hsub : Q₃.locus ⊆ Q₂.locus := hQ₃₂.trans_subset Set.inter_subset_left
  have hclopen := Q₃.isClopen_chart_preimage_of_eq_inter Q₂ hU₃ hQ₃₂
  obtain ⟨hrflat, hrsurj⟩ := Q₃.restriction_flat_and_surjective Q₂ hsub hclopen
  have hQ₃r : Set.range Q₃.chart ⊆ Set.range Q₂.chart := by
    rw [Q₃.range_chart, Q₂.range_chart]
    exact hsub
  have hcomm := g'.fullRecognitionPairs.restriction_comm Q₃ Q₂ Z Z hQ₃r
    (Set.Subset.refl _) hQ₃h hQ₂h
  rw [C.fullRecognitionPresentation.atlas.restriction_id Z (Set.Subset.refl _),
    BoundedAlgHom.comp_id] at hcomm
  -- the piece of `g` over the new piece `Q₃`
  have hQ₃U : Q₃.locus ⊆ U := (hQ₃.trans_subset Set.inter_subset_left).trans hU₃U
  have hxQ₃ : g.baseMap y ∈ Q₃.locus := hQ₃ ▸ ⟨hx₃, hzZ'⟩
  obtain ⟨P₁, hP₁h, hP₁, hP₁fin⟩ := hfin.2 Q₃ hQ₃U
  have hVP : V'' = P₁ := by
    apply Subtype.ext
    apply Subtype.ext
    change V''.locus = P₁.locus
    rw [hV'', hP₁, hQ₃]
    ext p
    constructor
    · rintro ⟨⟨hpV, hpU⟩, hpZ⟩
      exact ⟨hpV, hpU, hpZ⟩
    · rintro ⟨hpV, hpU, hpZ⟩
      exact ⟨⟨hpV, hpU⟩, hpZ⟩
  subst hVP
  rw [fullRecognitionPairs_comp g g' V'' Q₃ Z hP₁h hQ₃h h'']
  have hsQ : Q₃.chart (BanachSpectrum.comap
      (g.fullRecognitionPairs.pullback V'' Q₃ hP₁h).toBoundedRingHom s) = g.baseMap y := by
    rw [← hs]
    exact g.fullRecognitionPairs.chart_comm V'' Q₃ hP₁h s
  refine hcomp _ _ s hP₁fin.finite.finiteType hQ₃fin.finite.finiteType
    (hQg Q₃ hQ₃U hxQ₃ V'' hP₁h hP₁ s hs) ?_
  rw [← hcomm]
  set t := BanachSpectrum.comap (g.fullRecognitionPairs.pullback V'' Q₃ hP₁h).toBoundedRingHom s
  refine hcomp _ _ t (Q₃.restriction_finite Q₂ hsub hclopen).finiteType
    ?_ (hres _ hrflat hrsurj t) ?_
  · exact hQ₂fin.finite.finiteType
  · exact hQg' Z (hZT.trans hT₃T₂) hzZ' Q₂ hQ₂h hQ₂ _
      ((Q₃.chart_restriction Q₂ hsub t).trans hsQ)

/-- Berkovich's Corollary 3.2.6 for compositions, pointwise: flatness over all
pieces composes. -/
theorem IsFlatAtAllPieces.comp {y : A.space} (hg : g.IsFlatAtAllPieces y)
    (hg' : g'.IsFlatAtAllPieces (g.baseMap y)) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFlatAtAllPieces y :=
  HasAllPiecesAt.comp (Q := fun _ _ f s => f.IsFlatAtPoint s)
    (fun _ _ _ _ _ _ _ _ hf hf' => hf.comp hf')
    (fun _ _ r hr _ z => r.isFlatAtPoint_of_flat hr z) hg hg'

/-- Unramifiedness over all pieces composes. -/
theorem IsUnramifiedAtAllPieces.comp {y : A.space} (hg : g.IsUnramifiedAtAllPieces y)
    (hg' : g'.IsUnramifiedAtAllPieces (g.baseMap y)) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsUnramifiedAtAllPieces y :=
  HasAllPiecesAt.comp (Q := fun _ _ f s => f.IsUnramifiedAtPoint s)
    (fun _ _ _ _ _ _ hft hf't hf hf' => BoundedAlgHom.IsUnramifiedAtPoint.comp hft hf't hf hf')
    (fun _ _ r _ hs z => r.isUnramifiedAtPoint_of_formallyUnramified
      (RingHom.FormallyUnramified.of_surjective hs) z) hg hg'

/-- Berkovich's Corollary 3.3.8 for compositions, pointwise: étaleness over
all pieces composes. -/
theorem IsEtaleAtAllPieces.comp {y : A.space} (hg : g.IsEtaleAtAllPieces y)
    (hg' : g'.IsEtaleAtAllPieces (g.baseMap y)) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAtAllPieces y := by
  obtain ⟨V, hV, hy, hVe⟩ := hg
  obtain ⟨V', hV', hy', hV'e⟩ := hg'
  refine ⟨V ∩ g.baseMap ⁻¹' V', hV.inter (hV'.preimage g.baseMap.continuous), ⟨hy, hy'⟩,
    fun z hz => ⟨?_, ?_⟩⟩
  · exact (hVe z hz.1).1.comp (hV'e (g.baseMap z) hz.2).1
  · exact (hVe z hz.1).2.comp (hV'e (g.baseMap z) hz.2).2

/-- Étale morphisms over all pieces compose. -/
theorem IsEtaleAllPieces.comp (hg : g.IsEtaleAllPieces) (hg' : g'.IsEtaleAllPieces) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAllPieces :=
  fun y => (hg y).comp (hg' (g.baseMap y))

end Composition

variable (A) in
theorem isEtaleAllPieces_id : (StrongHom.id A.saturatedPresentation).IsEtaleAllPieces :=
  (isFiniteEtale_id A).isEtaleAllPieces

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
