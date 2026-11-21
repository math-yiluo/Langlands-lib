import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.FiniteEtaleOverRecognition
import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.RecognizedContainedDomain

/-! # Reflection of étaleness on affine analytification charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set CategoryTheory AffinoidAtlasPresentation IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
private theorem finiteEtale_of_heq {R S R' S' : PresentedAffinoidAlgebra K}
    {f : BoundedAlgHom K R S} {f' : BoundedAlgHom K R' S'}
    (hR : R = R') (hS : S = S') (hf : HEq f f')
    (h : f.IsFiniteBanach ∧ f.AlgebraicallyFiniteEtale) :
    f'.IsFiniteBanach ∧ f'.AlgebraicallyFiniteEtale := by
  subst R'
  subst S'
  cases eq_of_heq hf
  exact h

omit [CompleteSpace K] in
private theorem finiteEtale_toBoundedAlgHom (R S : PresentedAffinoidAlgebra K)
    (e : BoundedAlgEquiv K R S) :
    e.toBoundedAlgHom.IsFiniteBanach ∧ e.toBoundedAlgHom.AlgebraicallyFiniteEtale :=
  ⟨e.isFiniteBanach, BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _ e.bijective⟩

private theorem originalRecognition_locus {X : Type v} [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, v, w} K X) (i : a.Index) :
    (a.originalRecognitionIndex i).locus = range (a.chart i) :=
  (a.originalRecognitionIndex i).range_chart.symm.trans (a.recognitionAtlas_original_range i)

private theorem originalRecognition_chart_range {X : Type v} [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, v, w} K X) (i : a.Index) :
    range (a.originalRecognitionIndex i).chart = range (a.chart i) :=
  (a.originalRecognitionIndex i).range_chart.trans (originalRecognition_locus a i)

private theorem exists_originalRecognitionIndex_of_subset {X : Type v} [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, v, w} K X) (ha : a.HasAllLocalDomains)
    (W : a.RecognizedSubset) (i : a.Index) (hW : W.locus ⊆ range (a.chart i)) :
    ∃ j, a.originalRecognitionIndex j = W := by
  let L : LocalDomain a := ⟨i, W.containedDomain i hW⟩
  obtain ⟨j, hj⟩ := ha.exists_chart L
  exact ⟨j, Subtype.ext (Subtype.ext ((originalRecognition_locus a j).trans
    (hj.trans (Set.image_preimage_eq_of_subset hW))))⟩

namespace IndexedAffinoidAtlas

/-- A recognized subset of the double saturation contained in a chart of the
first saturation is lifted from a chart of the first saturation. -/
def liftedRecognitionIndexOfSubset {X : Type v} [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, v, w} K X) (P : a.saturatedAtlas.saturatedAtlas.RecognizedSubset)
    (i : a.saturatedAtlas.Index) (hP : P.locus ⊆ range (a.saturatedAtlas.chart i)) :
    { j : a.saturatedAtlas.Index // a.saturatedAtlas.saturatedAtlas.originalRecognitionIndex
      (a.saturatedAtlas.originalSaturatedIndex j) = P } := by
  let b := a.saturatedAtlas
  obtain ⟨J, hJ⟩ := Classical.indefiniteDescription _
    (exists_originalRecognitionIndex_of_subset b.saturatedAtlas
      b.saturatedAtlas_hasAllLocalDomains P (b.originalSaturatedIndex i)
      (hP.trans (b.saturatedAtlas_original_range i).symm.subset))
  obtain ⟨j, hj⟩ := Classical.indefiniteDescription _
    (a.saturatedAtlas_hasAllLocalDomains.exists_chart (b.saturatedRepresentative J))
  have hjJ : b.originalSaturatedIndex j = J :=
    b.saturatedAtlas.chartDomain_injective ((b.saturatedAtlas_original_range j).trans
      (hj.trans (b.saturatedRepresentative J).range_ambientMap.symm))
  exact ⟨j, (congrArg b.saturatedAtlas.originalRecognitionIndex hjJ).trans hJ⟩

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

private theorem originalRecognition_finiteEtale_iff
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (h : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (h' : g.baseMap '' range (A.atlas.saturatedAtlas.originalRecognitionIndex i).chart ⊆
      range (B.atlas.saturatedAtlas.originalRecognitionIndex j).chart) :
    ((g.fullRecognitionPairs.pullback _ _ h').IsFiniteBanach ∧
      (g.fullRecognitionPairs.pullback _ _ h').AlgebraicallyFiniteEtale) ↔
    ((g.pullback i j h).IsFiniteBanach ∧ (g.pullback i j h).AlgebraicallyFiniteEtale) := by
  let a := A.atlas.saturatedAtlas
  let b := B.atlas.saturatedAtlas
  let V := a.originalRecognitionIndex i
  let W := b.originalRecognitionIndex j
  let eV := a.originalRecognitionRestrictionEquiv i
  let eW := b.originalRecognitionRestrictionEquiv j
  let p : BoundedAlgHom K (b.algebra j) (a.algebra i) := g.pullback i j h
  let q : BoundedAlgHom K W.algebra V.algebra := g.fullRecognitionPairs.pullback V W h'
  change (q.IsFiniteBanach ∧ q.AlgebraicallyFiniteEtale) ↔
    (p.IsFiniteBanach ∧ p.AlgebraicallyFiniteEtale)
  have hcomm : eV.toBoundedAlgHom.comp q = p.comp eW.toBoundedAlgHom := by
    change (a.originalRecognitionRestrictionEquiv i).toBoundedAlgHom.comp q =
      p.comp (b.originalRecognitionRestrictionEquiv j).toBoundedAlgHom
    rw [a.originalRecognitionRestrictionEquiv_toBoundedAlgHom,
      b.originalRecognitionRestrictionEquiv_toBoundedAlgHom]
    exact g.originalRestriction_comp_fullRecognitionPairs V W h' i
      (a.originalRecognitionIndex_range_subset i) j (b.originalRecognitionIndex_range_subset j) h
  have happ (x : W.algebra) : eV (q x) = p (eW x) :=
    congrArg (fun r : BoundedAlgHom K W.algebra (a.algebra i) => r x) hcomm
  constructor
  · intro hq
    have hp : p = (eV.toBoundedAlgHom.comp q).comp eW.symm.toBoundedAlgHom := by
      apply BoundedAlgHom.ext
      intro x
      change p x = eV (q (eW.symm x))
      exact (congrArg (fun t => p t) (eW.apply_symm_apply x)).symm.trans
        (happ (eW.symm x)).symm
    rw [hp]
    have hV := finiteEtale_toBoundedAlgHom _ _ eV
    have hW := finiteEtale_toBoundedAlgHom _ _ eW.symm
    exact ⟨(hV.1.comp hq.1).comp hW.1, (hV.2.comp hq.2).comp hW.2⟩
  · intro hp
    have hq : q = (eV.symm.toBoundedAlgHom.comp p).comp eW.toBoundedAlgHom := by
      apply BoundedAlgHom.ext
      intro x
      change q x = eV.symm (p (eW x))
      exact (eV.symm_apply_apply (q x)).symm.trans (congrArg (fun t => eV.symm t) (happ x))
    rw [hq]
    have hV := finiteEtale_toBoundedAlgHom _ _ eV.symm
    have hW := finiteEtale_toBoundedAlgHom _ _ eW
    exact ⟨(hV.1.comp hp.1).comp hW.1, (hV.2.comp hp.2).comp hW.2⟩

private theorem finiteEtale_of_saturationExtension
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (hg : g.HasCoherentPullbacks)
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (h : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (h' : g.baseMap '' range (A.atlas.saturatedAtlas.originalRecognitionIndex i).chart ⊆
      range (B.atlas.saturatedAtlas.originalRecognitionIndex j).chart)
    (h'' : (g.saturationExtension hg).baseMap '' range
        (A.atlas.saturatedAtlas.saturatedAtlas.originalRecognitionIndex
          (A.atlas.saturatedAtlas.originalSaturatedIndex i)).chart ⊆
      range (B.atlas.saturatedAtlas.saturatedAtlas.originalRecognitionIndex
        (B.atlas.saturatedAtlas.originalSaturatedIndex j)).chart)
    (he : ((g.saturationExtension hg).fullRecognitionPairs.pullback _ _ h'').IsFiniteBanach ∧
      ((g.saturationExtension hg).fullRecognitionPairs.pullback _ _ h'').AlgebraicallyFiniteEtale) :
    (g.fullRecognitionPairs.pullback _ _ h').IsFiniteBanach ∧
      (g.fullRecognitionPairs.pullback _ _ h').AlgebraicallyFiniteEtale := by
  have hG := (originalRecognition_finiteEtale_iff (A := A.saturatedPresentation)
    (B := B.saturatedPresentation) (g.saturationExtension hg)
    (A.atlas.saturatedAtlas.originalSaturatedIndex i)
    (B.atlas.saturatedAtlas.originalSaturatedIndex j)
    (g.saturationExtension_original_admissible i j h) h'').mp he
  have hmap := g.saturationExtension_pullback_original hg i j h
  exact (originalRecognition_finiteEtale_iff g i j h h').mpr
    (finiteEtale_of_heq (B.atlas.saturatedAtlas.saturatedAtlas_original_algebra j)
      (A.atlas.saturatedAtlas.saturatedAtlas_original_algebra i) hmap hG)

set_option maxHeartbeats 800000 in
/-- If both first saturations are covered by chart interiors, canonical strong
étaleness gives étaleness over finite recognized families in the first
saturations, with any common universe for the original chart indices. -/
private theorem isEtale_of_strongEtale_of_chart_interiors
    (g : SaturatedAtlasPresentation.ofSaturation A ⟶ SaturatedAtlasPresentation.ofSaturation B)
    (hg : SaturatedAtlasPresentation.strongEtale g)
    (hA : ∀ y : A.space, ∃ i : A.atlas.saturatedAtlas.Index,
      y ∈ interior (range (A.atlas.saturatedAtlas.chart i)))
    (hB : ∀ x : B.space, ∃ j : B.atlas.saturatedAtlas.Index,
      x ∈ interior (range (B.atlas.saturatedAtlas.chart j))) :
    IsEtale (A := A) (B := B) g := by
  let hc := g.hasCoherentPullbacks_of_saturated A.atlas.saturatedAtlas_hasAllLocalDomains
  let G : StrongHom A.saturatedPresentation.saturatedPresentation
      B.saturatedPresentation.saturatedPresentation := g.saturationExtension hc
  have hG : IsEtaleAllPieces (A := A.saturatedPresentation) (B := B.saturatedPresentation) G := hg
  apply isEtale_iff_forall_isEtaleAt.mpr
  intro y
  apply IsLocallyFiniteEtaleAt.isEtaleAt
  obtain ⟨i₀, hi₀⟩ := hA y
  obtain ⟨j₀, hj₀⟩ := hB (g.baseMap y)
  obtain ⟨V, U, hV, hU, hyV, hVi, hfin⟩ :=
    (strongEtaleLocallyFiniteEtale _ _ G hG y).isFiniteAt.exists_small
      (isOpen_interior.mem_nhds hi₀)
  let U' : Set B.space := U ∩ interior (range (B.atlas.saturatedAtlas.chart j₀))
  let V' : Set A.space := V ∩ G.baseMap ⁻¹' U'
  have hU' : IsOpen U' := hU.inter isOpen_interior
  have hV' : IsOpen V' := hV.inter (hU'.preimage G.baseMap.continuous)
  have hyV' : y ∈ V' := ⟨hyV, hfin.1 ⟨y, hyV, rfl⟩, hj₀⟩
  have hfe : G.IsFiniteEtaleOver V' U' :=
    hG.isFiniteEtaleOver hV' (hfin.restrictTarget inter_subset_left)
  refine ⟨V', U', hV', hU', hyV', hfe.1, ?_⟩
  intro W hWU
  obtain ⟨j, hj⟩ := exists_originalRecognitionIndex_of_subset B.atlas.saturatedAtlas
    B.atlas.saturatedAtlas_hasAllLocalDomains W j₀
    (hWU.trans (inter_subset_right.trans interior_subset))
  subst W
  let J : B.atlas.saturatedAtlas.saturatedAtlas.Index :=
    B.atlas.saturatedAtlas.originalSaturatedIndex j
  let W' : B.atlas.saturatedAtlas.saturatedAtlas.RecognizedSubset :=
    B.atlas.saturatedAtlas.saturatedAtlas.originalRecognitionIndex J
  have hW'locus : W'.locus = (B.atlas.saturatedAtlas.originalRecognitionIndex j).locus :=
    (originalRecognition_locus B.atlas.saturatedAtlas.saturatedAtlas J).trans
      ((B.atlas.saturatedAtlas.saturatedAtlas_original_range j).trans
        (originalRecognition_locus B.atlas.saturatedAtlas j).symm)
  obtain ⟨P', hP'W', hP', hP'fe⟩ := hfe.2 W' (hW'locus.trans_subset hWU)
  obtain ⟨i, hi⟩ := A.atlas.liftedRecognitionIndexOfSubset P' i₀
    (hP'.trans_subset (inter_subset_left.trans (inter_subset_left.trans
      (hVi.trans interior_subset))))
  subst P'
  let I : A.atlas.saturatedAtlas.saturatedAtlas.Index :=
    A.atlas.saturatedAtlas.originalSaturatedIndex i
  let P : A.atlas.saturatedAtlas.RecognizedSubset := A.atlas.saturatedAtlas.originalRecognitionIndex i
  have hP'locus : (A.atlas.saturatedAtlas.saturatedAtlas.originalRecognitionIndex I).locus =
      P.locus :=
    (originalRecognition_locus A.atlas.saturatedAtlas.saturatedAtlas I).trans
      ((A.atlas.saturatedAtlas.saturatedAtlas_original_range i).trans
        (originalRecognition_locus A.atlas.saturatedAtlas i).symm)
  have hP'range := (originalRecognition_chart_range A.atlas.saturatedAtlas.saturatedAtlas I).trans
    (A.atlas.saturatedAtlas.saturatedAtlas_original_range i)
  have hW'range := (originalRecognition_chart_range B.atlas.saturatedAtlas.saturatedAtlas J).trans
    (B.atlas.saturatedAtlas.saturatedAtlas_original_range j)
  have hPW : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j) :=
    (Set.image_mono hP'range.symm.subset).trans (hP'W'.trans hW'range.subset)
  have h : g.baseMap '' range P.chart ⊆
      range (B.atlas.saturatedAtlas.originalRecognitionIndex j).chart :=
    (Set.image_mono (originalRecognition_chart_range A.atlas.saturatedAtlas i).subset).trans
      (hPW.trans (originalRecognition_chart_range B.atlas.saturatedAtlas j).symm.subset)
  have hpreimage := congrArg (fun Z : Set B.space => V' ∩ g.baseMap ⁻¹' Z) hW'locus
  exact ⟨P, h, hP'locus.symm.trans (hP'.trans hpreimage),
    finiteEtale_of_saturationExtension g hc i j hPW h hP'W' hP'fe⟩

end AffinoidAtlasPresentation.StrongHom

namespace AffineAnalytification

open SaturatedAtlasPresentation

variable {k : Type u} [NontriviallyNormedField k] [IsUltrametricDist k] [CompleteSpace k]
  {R : Type v} [CommRing R] [Algebra k R] {S : Type w} [CommRing S] [Algebra k S]

private theorem exists_saturated_chart_interior
    (P : FinitePolynomialPresentation k R) (x : Space k P) :
    ∃ i : (atlas k P).saturatedAtlas.Index,
      x ∈ interior (range ((atlas k P).saturatedAtlas.chart i)) := by
  obtain ⟨m, s, hs⟩ := exists_chart k P x
  let i : (atlas k P).Index := representative k P (m + 1)
  refine ⟨(atlas k P).originalSaturatedIndex i, ?_⟩
  rw [(atlas k P).saturatedAtlas_original_range]
  change x ∈ interior (range (chart k P (representative k P (m + 1)).val))
  rw [range_representative k P, mem_interior_iff_mem_nhds]
  exact range_chart_mem_nhds k P ⟨s, hs⟩

/-- Localized étaleness of the actual affine analytification gives the
finite-pieces étale predicate for its original index-zero presentation. -/
theorem isEtale_of_localizedHom_etale
    (P : FinitePolynomialPresentation k R) (Q : FinitePolynomialPresentation k S)
    (f : R →ₐ[k] S) (hf : etale (localizedHom k P Q f)) :
    StrongHom.IsEtale (A := presentation k Q) (B := presentation k P)
      (saturatedHom k P Q f) :=
  StrongHom.isEtale_of_strongEtale_of_chart_interiors (saturatedHom k P Q f)
    ((etale_localizationFunctor_map_iff_strongEtale _).mp hf)
    (exists_saturated_chart_interior Q) (exists_saturated_chart_interior P)

end AffineAnalytification
end Langlands.Analytic
