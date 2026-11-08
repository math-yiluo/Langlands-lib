import Langlands.Geometry.Analytic.PairSystemLocalizedMorphisms

/-! # The isomorphism criterion through full-recognition pair systems -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

variable {A B : PresentedAffinoidAlgebra K}

/-- The inverse supplied by the universal property of a representation of the
whole spectrum. -/
def Represents.univInverse {f : BoundedAlgHom K A B} (hf : Represents K f Set.univ) :
    BoundedAlgHom K B A :=
  (hf.2.2 A (BoundedAlgHom.id K A) fun _ => Set.mem_univ _).exists.choose

theorem Represents.univInverse_comp {f : BoundedAlgHom K A B} (hf : Represents K f Set.univ) :
    hf.univInverse.comp f = BoundedAlgHom.id K A :=
  (hf.2.2 A (BoundedAlgHom.id K A) fun _ => Set.mem_univ _).exists.choose_spec

theorem Represents.comp_univInverse {f : BoundedAlgHom K A B} (hf : Represents K f Set.univ) :
    f.comp hf.univInverse = BoundedAlgHom.id K B :=
  (hf.2.2 B f fun _ => Set.mem_univ _).unique
    (by rw [BoundedAlgHom.comp_assoc, hf.univInverse_comp]; rfl) rfl

/-- A representation of the whole spectrum is a bounded algebra equivalence. -/
def Represents.univEquiv {f : BoundedAlgHom K A B} (hf : Represents K f Set.univ) :
    BoundedAlgEquiv K A B :=
  BoundedAlgEquiv.ofHomInv f hf.univInverse
    (fun a => congrArg (fun q : BoundedAlgHom K A A => q a) hf.univInverse_comp)
    (fun b => congrArg (fun q : BoundedAlgHom K B B => q b) hf.comp_univInverse)

theorem Represents.univEquiv_toBoundedAlgHom {f : BoundedAlgHom K A B}
    (hf : Represents K f Set.univ) : hf.univEquiv.toBoundedAlgHom = f :=
  BoundedAlgHom.ext fun _ => rfl

end PresentedAffinoidAlgebra

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

theorem originalRecognitionIndex_range_subset (i : a.Index) :
    Set.range (a.chart i) ⊆ (a.originalRecognitionIndex i).locus :=
  (a.recognitionAtlas_original_range i).symm.subset.trans
    (RecognizedSubset.range_chart (a.originalRecognitionIndex i)).subset

/-- The canonical restriction from an original chart, viewed as a recognized
subset, to the chart itself represents the whole spectrum. -/
theorem originalRecognition_originalRestriction_represents_univ (i : a.Index) :
    Represents K ((a.originalRecognitionIndex i).originalRestriction i
      (a.originalRecognitionIndex_range_subset i)) Set.univ := by
  have h := (a.originalRecognitionIndex i).originalRestriction_represents i
    (a.originalRecognitionIndex_range_subset i)
  rw [(a.originalRecognitionIndex i).range_comap_originalRestriction] at h
  have hu : (a.originalRecognitionIndex i).chart ⁻¹' Set.range (a.chart i) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact (a.recognitionAtlas_original_range i).subset (Set.mem_range_self x)
  rw [hu] at h
  exact h

/-- The resulting bounded algebra equivalence. -/
def originalRecognitionRestrictionEquiv (i : a.Index) :
    BoundedAlgEquiv K (a.originalRecognitionIndex i).algebra (a.algebra i) :=
  (a.originalRecognition_originalRestriction_represents_univ i).univEquiv

theorem originalRecognitionRestrictionEquiv_toBoundedAlgHom (i : a.Index) :
    (a.originalRecognitionRestrictionEquiv i).toBoundedAlgHom =
      (a.originalRecognitionIndex i).originalRestriction i
        (a.originalRecognitionIndex_range_subset i) :=
  Represents.univEquiv_toBoundedAlgHom _

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

/-- Isomorphism criterion, sufficient direction, on original local domains:
an ambient homeomorphism whose pair system identifies the recognized subset of
every source local domain with a recognized target subset with the image locus
is a strong quasi-isomorphism. -/
theorem isQuasiIso_of_originalImages (hh : IsHomeomorph g.baseMap)
    (himg : ∀ S : A.atlas.saturatedAtlas.Index,
      ∃ (W : B.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range (A.atlas.saturatedAtlas.originalRecognitionIndex S).chart ⊆
          Set.range W.chart),
        W.locus = g.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) ∧
        ∃ e : BoundedAlgEquiv K W.algebra
            (A.atlas.saturatedAtlas.originalRecognitionIndex S).algebra,
          e.toBoundedAlgHom = g.fullRecognitionPairs.pullback
            (A.atlas.saturatedAtlas.originalRecognitionIndex S) W h) :
    g.IsQuasiIso := by
  refine ⟨hh, fun S T hST => ?_⟩
  let V : A.atlas.saturatedAtlas.RecognizedSubset :=
    A.atlas.saturatedAtlas.originalRecognitionIndex S
  let WT : B.atlas.saturatedAtlas.RecognizedSubset :=
    B.atlas.saturatedAtlas.originalRecognitionIndex T
  obtain ⟨W, hVW, hWloc, e, he⟩ := himg S
  have hS := A.atlas.saturatedAtlas.originalRecognitionIndex_range_subset S
  have hT := B.atlas.saturatedAtlas.originalRecognitionIndex_range_subset T
  have hWWT : W.locus ⊆ WT.locus := hWloc.trans_subset (hST.trans hT)
  have hWWT' : Set.range (B.fullRecognitionPresentation.atlas.chart W) ⊆
      Set.range (B.fullRecognitionPresentation.atlas.chart WT) :=
    W.range_chart.trans_subset (hWWT.trans WT.range_chart.superset)
  have hVWT : g.baseMap '' Set.range V.chart ⊆ Set.range WT.chart :=
    hVW.trans hWWT'
  have hchar := g.originalRestriction_comp_fullRecognitionPairs V WT hVWT S hS T hT hST
  have hres := g.fullRecognitionPairs.restriction_comm V V W WT Set.Subset.rfl hWWT' hVW hVWT
  have hself : (A.fullRecognitionPresentation.atlas.restriction V V Set.Subset.rfl) =
      BoundedAlgHom.id K V.algebra := V.restriction_self
  rw [hself] at hres
  let ι := B.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv T
  let σ := A.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv S
  have hr := W.restriction_represents WT hWWT
  have hr1 := hr.postcomp_equiv e
  have hr2 := hr1.postcomp_equiv σ
  have hr3 := hr2.precomp_equiv ι
  have hkey : (g.pullback S T hST).comp ι.toBoundedAlgHom =
      σ.toBoundedAlgHom.comp (e.toBoundedAlgHom.comp (W.restriction WT hWWT)) :=
    hchar.symm.trans ((congrArg (fun q => BoundedAlgHom.comp (V.originalRestriction S hS) q)
      hres).trans (congrArg (fun q => BoundedAlgHom.comp (V.originalRestriction S hS)
        (BoundedAlgHom.comp q (W.restriction WT hWWT))) he.symm))
  have hmap : g.pullback S T hST =
      ((σ.toBoundedAlgHom.comp (e.toBoundedAlgHom.comp (W.restriction WT hWWT))).comp
        ι.symm.toBoundedAlgHom) := by
    apply BoundedAlgHom.ext
    intro b
    have h1 := congrArg (fun q : BoundedAlgHom K WT.algebra
      (A.atlas.saturatedAtlas.algebra S) => q (ι.symm b)) hkey
    exact (congrArg (fun z => g.pullback S T hST z) (ι.apply_symm_apply b)).symm.trans h1
  have hx : ∀ x, WT.chart (ι.spectrumHomeomorph x) = B.atlas.saturatedAtlas.chart T x :=
    fun x => WT.chart_originalRestriction T hT x
  have hloc : g.chartImageLocus S T =
      ι.spectrumHomeomorph ⁻¹' (WT.chart ⁻¹' W.locus) := by
    ext x
    change B.atlas.saturatedAtlas.chart T x ∈
        g.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) ↔
      WT.chart (ι.spectrumHomeomorph x) ∈ W.locus
    rw [hx x, hWloc]
    exact Iff.rfl
  exact (congrArg₂ (fun f U => Represents K f U) hmap hloc).mpr hr3

/-- The conditions of Berkovich's isomorphism criterion (Proposition
1.2.15(ii)) for the full-recognition pair system: the ambient map is a
homeomorphism, and every recognized affinoid subset `V` has a recognized image
`W` whose bounded map `W → V` in the pair system is an isomorphism of affinoid
algebras. -/
def IsomorphismCriterion : Prop :=
  IsHomeomorph g.baseMap ∧
    ∀ V : A.atlas.saturatedAtlas.RecognizedSubset,
      ∃ (W : B.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart),
        W.locus = g.baseMap '' V.locus ∧
        ∃ e : BoundedAlgEquiv K W.algebra V.algebra,
          e.toBoundedAlgHom = g.fullRecognitionPairs.pullback V W h

/-- Isomorphism criterion, sufficient direction (Proposition 1.2.15(ii)): a
strong map satisfying the criterion is a strong quasi-isomorphism. -/
theorem IsomorphismCriterion.isQuasiIso (hg : g.IsomorphismCriterion) : g.IsQuasiIso := by
  refine g.isQuasiIso_of_originalImages hg.1 fun S => ?_
  obtain ⟨W, h, hW, e, he⟩ := hg.2 (A.atlas.saturatedAtlas.originalRecognitionIndex S)
  refine ⟨W, h, hW.trans (congrArg (fun s => g.baseMap '' s)
    ((RecognizedSubset.range_chart (A.atlas.saturatedAtlas.originalRecognitionIndex S)).symm.trans
      (A.atlas.saturatedAtlas.recognitionAtlas_original_range S))), e, he⟩

/-- The strong map as a morphism of the saturated strong category. -/
def saturatedHom :
    SaturatedAtlasPresentation.ofSaturation A ⟶ SaturatedAtlasPresentation.ofSaturation B :=
  g

/-- Under the criterion, the localized strong map is an isomorphism. -/
theorem IsomorphismCriterion.isIso_localizationFunctor_map (hg : g.IsomorphismCriterion) :
    IsIso (SaturatedAtlasPresentation.localizationFunctor.map g.saturatedHom) :=
  (SaturatedAtlasPresentation.localizedQuasiIso g.saturatedHom hg.isQuasiIso).isIso_hom

/-- For a quasi-isomorphism of local-domain enlargements, the morphism of the
full recognitions constructed from its pair system is an isomorphism of the
localized category. -/
theorem isIso_fullRecognitionLocalizedHom (hq : g.IsQuasiIso) :
    IsIso g.fullRecognitionLocalizedHom := by
  have hA : IsIso (SaturatedAtlasPresentation.localizationFunctor.map
      (localDomainToFullRecognitionHom A)) :=
    (SaturatedAtlasPresentation.localizedQuasiIso
      (localDomainToFullRecognitionHom A) A.localDomainToFullRecognition_isQuasiIso).isIso_hom
  have hB : IsIso (SaturatedAtlasPresentation.localizationFunctor.map
      (localDomainToFullRecognitionHom B)) :=
    (SaturatedAtlasPresentation.localizedQuasiIso
      (localDomainToFullRecognitionHom B) B.localDomainToFullRecognition_isQuasiIso).isIso_hom
  have hg : IsIso (SaturatedAtlasPresentation.localizationFunctor.map g.saturatedHom) :=
    (SaturatedAtlasPresentation.localizedQuasiIso g.saturatedHom hq).isIso_hom
  have hcomp : g.saturatedHom ≫ localDomainToFullRecognitionHom B =
      g.toFullRecognitionTargetHom := rfl
  have hiso : IsIso (SaturatedAtlasPresentation.localizationFunctor.map
      g.toFullRecognitionTargetHom) := by
    rw [← hcomp, Functor.map_comp]
    infer_instance
  rw [← g.localizationFunctor_map_comp_fullRecognitionLocalizedHom] at hiso
  exact IsIso.of_isIso_comp_left
    (SaturatedAtlasPresentation.localizationFunctor.map (localDomainToFullRecognitionHom A))
    g.fullRecognitionLocalizedHom

/-- Under the criterion, the morphism of full recognitions constructed from
the pair system is an isomorphism of the localized category. -/
theorem IsomorphismCriterion.isIso_fullRecognitionLocalizedHom
    (hg : g.IsomorphismCriterion) : IsIso g.fullRecognitionLocalizedHom :=
  g.isIso_fullRecognitionLocalizedHom hg.isQuasiIso

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
