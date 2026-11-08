import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain

/-! # Flat, unramified and étale quasifinite morphisms through full-recognition pair systems -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Every neighborhood of a point contains finitely many recognized affinoid
subsets of the full recognition that contain the point and whose union is
again a neighborhood of the point. They are recognized local domains given by
rational charts of the original charts. -/
theorem exists_finite_recognized_nhds_subset (x : X) (U : Set X) (hU : U ∈ 𝓝 x) :
    ∃ I : Set a.saturatedAtlas.RecognizedSubset, I.Finite ∧
      (∀ W ∈ I, x ∈ W.locus ∧ W.locus ⊆ U) ∧ (⋃ W ∈ I, W.locus) ∈ 𝓝 x := by
  obtain ⟨σ, hσfin, hστ, hxσ, hσN⟩ := a.isNet_chartFamily.1 x
  have key : ∀ V ∈ σ, ∃ W : a.saturatedAtlas.RecognizedSubset,
      x ∈ W.locus ∧ W.locus ⊆ U ∧ ∃ t ∈ 𝓝 x, t ∩ V ⊆ W.locus := by
    intro V hV
    obtain ⟨i, rfl⟩ := hστ hV
    obtain ⟨s, hs⟩ := hxσ _ hV
    have hpre : a.chart i ⁻¹' U ∈ 𝓝 s :=
      (a.isEmbedding_chart i).continuous.continuousAt.preimage_mem_nhds (hs ▸ hU)
    obtain ⟨d, hdN, hdU⟩ := RationalChart.exists_rational_neighborhood s _ hpre
    let D : LocalDomain a := ⟨i, d.toDomain⟩
    have hD : (a.recognizedLocalDomain D).locus = a.chart i '' d.locus :=
      a.recognizedLocalDomain_locus D
    refine ⟨a.recognizedLocalDomain D, ?_, ?_, ?_⟩
    · rw [hD]
      exact ⟨s, mem_of_mem_nhds hdN, hs⟩
    · rw [hD]
      rintro _ ⟨s', hs', rfl⟩
      exact hdU hs'
    · rw [(a.isEmbedding_chart i).nhds_eq_comap, Filter.mem_comap] at hdN
      obtain ⟨t, ht, hts⟩ := hdN
      refine ⟨t, hs ▸ ht, ?_⟩
      rintro y ⟨hyt, s', rfl⟩
      rw [hD]
      exact ⟨s', hts hyt, rfl⟩
  choose W hWx hWU t ht htW using key
  refine ⟨{W' | ∃ V hV, W V hV = W'}, hσfin.dependent_image W, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨hWx V hV, hWU V hV⟩
  · have hT : ⋂₀ {t' | ∃ V hV, t V hV = t'} ∈ 𝓝 x := by
      refine (Filter.sInter_mem (hσfin.dependent_image t)).2 ?_
      rintro _ ⟨V, hV, rfl⟩
      exact ht V hV
    refine Filter.mem_of_superset (Filter.inter_mem hσN hT) ?_
    rintro y ⟨⟨V, hV, hyV⟩, hyt⟩
    exact Set.mem_biUnion (⟨V, hV, rfl⟩ : ∃ V' hV', W V' hV' = W V hV)
      (htW V hV ⟨hyt _ ⟨V, hV, rfl⟩, hyV⟩)

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

namespace StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Berkovich's Proposition 3.2.3(a) for a pointwise property `Q` of finite
affinoid maps: open neighborhoods `V` of `y` and `U` of its image between which
`g` induces a finite morphism, and finitely many recognized affinoid subsets of
`U` containing the image point, with union a neighborhood of it, over which
the induced finite affinoid maps have the property `Q` at the point `y`. -/
def HasFinitePiecesAt
    (Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) (y : A.space) : Prop :=
  ∃ (V : Set A.space) (U : Set B.space), IsOpen V ∧ IsOpen U ∧ y ∈ V ∧ g.IsFiniteOver V U ∧
    ∃ I : Set B.atlas.saturatedAtlas.RecognizedSubset, I.Finite ∧
      (∀ W ∈ I, W.locus ⊆ U ∧ g.baseMap y ∈ W.locus) ∧
      (⋃ W ∈ I, W.locus) ∈ 𝓝 (g.baseMap y) ∧
      ∀ W ∈ I, ∀ (V' : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus →
          ∀ s : BanachSpectrum V'.algebra, V'.chart s = y →
            Q (g.fullRecognitionPairs.pullback V' W h) s

/-- Berkovich's Definition 3.2.5: flatness at a point. -/
def IsFlatAt (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) : Prop :=
  g.HasFinitePiecesAt (fun _ _ f s => f.IsFlatAtPoint s) y

/-- Unramifiedness at a point, in the form of Proposition 3.3.7(b): the point
lies outside the support of the module of differentials of the finite affinoid
pieces. -/
def IsUnramifiedAt (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) : Prop :=
  g.HasFinitePiecesAt (fun _ _ f s => f.IsUnramifiedAtPoint s) y

/-- Flat quasifinite morphisms. -/
def IsFlat (g : StrongHom A.saturatedPresentation B.saturatedPresentation) : Prop :=
  ∀ y, g.IsFlatAt y

/-- Unramified quasifinite morphisms. -/
def IsUnramified (g : StrongHom A.saturatedPresentation B.saturatedPresentation) : Prop :=
  ∀ y, g.IsUnramifiedAt y

/-- Berkovich's Definition 3.3.4: étale morphisms are unramified and flat. -/
def IsEtale (g : StrongHom A.saturatedPresentation B.saturatedPresentation) : Prop :=
  g.IsUnramified ∧ g.IsFlat

/-- Étaleness at a point: an open neighborhood on which `g` is unramified and
flat. -/
def IsEtaleAt (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) : Prop :=
  ∃ V : Set A.space, IsOpen V ∧ y ∈ V ∧ ∀ y' ∈ V, g.IsUnramifiedAt y' ∧ g.IsFlatAt y'

section Basic

variable {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

theorem HasFinitePiecesAt.isFiniteAt
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    {y : A.space} (hg : g.HasFinitePiecesAt Q y) : g.IsFiniteAt y := by
  obtain ⟨V, U, hV, hU, hy, hfin, -⟩ := hg
  exact ⟨V, U, hV, hU, hy, hfin⟩

theorem HasFinitePiecesAt.mono
    {Q Q' : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hQ : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄ (f : BoundedAlgHom K R S) (s : BanachSpectrum S),
      Q f s → Q' f s)
    {y : A.space} (hg : g.HasFinitePiecesAt Q y) : g.HasFinitePiecesAt Q' y := by
  obtain ⟨V, U, hV, hU, hy, hfin, I, hI, hIU, hIN, hIQ⟩ := hg
  exact ⟨V, U, hV, hU, hy, hfin, I, hI, hIU, hIN,
    fun W hW V' h hV' s hs => hQ _ s (hIQ W hW V' h hV' s hs)⟩

theorem IsFlatAt.isFiniteAt {y : A.space} (hg : g.IsFlatAt y) : g.IsFiniteAt y :=
  HasFinitePiecesAt.isFiniteAt hg

theorem IsUnramifiedAt.isFiniteAt {y : A.space} (hg : g.IsUnramifiedAt y) :
    g.IsFiniteAt y :=
  HasFinitePiecesAt.isFiniteAt hg

theorem IsFlat.isQuasifinite (hg : g.IsFlat) : g.IsQuasifinite :=
  fun y => (hg y).isFiniteAt

theorem IsUnramified.isQuasifinite (hg : g.IsUnramified) : g.IsQuasifinite :=
  fun y => (hg y).isFiniteAt

theorem IsEtale.isQuasifinite (hg : g.IsEtale) : g.IsQuasifinite :=
  hg.2.isQuasifinite

theorem IsEtaleAt.isUnramifiedAt {y : A.space} (hg : g.IsEtaleAt y) : g.IsUnramifiedAt y := by
  obtain ⟨V, -, hy, hV⟩ := hg
  exact (hV y hy).1

theorem IsEtaleAt.isFlatAt {y : A.space} (hg : g.IsEtaleAt y) : g.IsFlatAt y := by
  obtain ⟨V, -, hy, hV⟩ := hg
  exact (hV y hy).2

theorem IsEtaleAt.isFiniteAt {y : A.space} (hg : g.IsEtaleAt y) : g.IsFiniteAt y :=
  hg.isFlatAt.isFiniteAt

/-- A morphism is étale if and only if it is étale at every point. -/
theorem isEtale_iff_forall_isEtaleAt : g.IsEtale ↔ ∀ y, g.IsEtaleAt y := by
  constructor
  · intro hg y
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ y, fun y' _ => ⟨hg.1 y', hg.2 y'⟩⟩
  · intro hg
    exact ⟨fun y => (hg y).isUnramifiedAt, fun y => (hg y).isFlatAt⟩

/-- A finite morphism between open sets whose affinoid pieces all have the
property `Q` at every point has finite pieces with `Q` at every point of the
source neighborhood. The pieces are supplied by the neighborhood basis of
recognized subsets. -/
theorem hasFinitePiecesAt_of_isFiniteOver
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    {V : Set A.space} {U : Set B.space} (hV : IsOpen V) (hU : IsOpen U)
    (hfin : g.IsFiniteOver V U)
    (hQ : ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ U →
      ∀ (V' : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus →
          ∀ s : BanachSpectrum V'.algebra, Q (g.fullRecognitionPairs.pullback V' W h) s)
    {y : A.space} (hy : y ∈ V) : g.HasFinitePiecesAt Q y := by
  have hUy : U ∈ 𝓝 (g.baseMap y) := hU.mem_nhds (hfin.1 ⟨y, hy, rfl⟩)
  obtain ⟨I, hI, hIU, hIN⟩ :=
    B.atlas.exists_finite_recognized_nhds_subset (g.baseMap y) U hUy
  exact ⟨V, U, hV, hU, hy, hfin, I, hI, fun W hW => ⟨(hIU W hW).2, (hIU W hW).1⟩, hIN,
    fun W hW V' h hV' s _ => hQ W (hIU W hW).2 V' h hV' s⟩

/-- Locally finite étale morphisms in the sense of `FullRecognitionFiniteMorphisms`
are étale at the point. -/
theorem IsLocallyFiniteEtaleAt.isEtaleAt {y : A.space} (hg : g.IsLocallyFiniteEtaleAt y) :
    g.IsEtaleAt y := by
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
  · exact hasFinitePiecesAt_of_isFiniteOver hV hU hfe.isFiniteOver
      (fun W hW V' h hV' s => (hpieces W hW V' h hV' s).2) hy'
  · exact hasFinitePiecesAt_of_isFiniteOver hV hU hfe.isFiniteOver
      (fun W hW V' h hV' s => (hpieces W hW V' h hV' s).1) hy'

/-- Finite morphisms with algebraically finite étale affinoid maps are étale. -/
theorem IsFiniteEtale.isEtale (hg : g.IsFiniteEtale) : g.IsEtale :=
  isEtale_iff_forall_isEtaleAt.2 fun y =>
    IsLocallyFiniteEtaleAt.isEtaleAt
      ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, Set.mem_univ y, hg⟩

end Basic

variable (A) in
/-- The identity of a local-domain enlargement is étale. -/
theorem isEtale_id : (StrongHom.id A.saturatedPresentation).IsEtale :=
  (isFiniteEtale_id A).isEtale

end StrongHom

end AffinoidAtlasPresentation

end Langlands.Analytic
