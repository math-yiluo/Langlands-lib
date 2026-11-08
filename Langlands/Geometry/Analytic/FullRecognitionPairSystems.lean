import Langlands.Geometry.Analytic.LocalDomainSubnetRecognition

/-! # Compatible affinoid pair systems on full recognition atlases -/

noncomputable section

universe u v w z v' w'

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas.RecognizedSubset

variable {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (V : a.RecognizedSubset) {R : Type z} [NormedCommRing R] [Algebra K R]

/-- Bounded maps into every original chart contained in `V`, compatible with
every original restriction between two such charts. -/
def IsChartCompatible
    (φ : ∀ k : a.Index, Set.range (a.chart k) ⊆ V.locus → BoundedAlgHom K R (a.algebra k)) :
    Prop :=
  ∀ (k l : a.Index) (hk : Set.range (a.chart k) ⊆ V.locus)
    (hl : Set.range (a.chart l) ⊆ V.locus)
    (hkl : Set.range (a.chart k) ⊆ Set.range (a.chart l)),
    (a.restriction k l hkl).comp (φ l hl) = φ k hk

/-- Each chart of the chosen special cover lies in the recognized subset. -/
theorem gluingIndex_subset (i : Fin V.val.gluingData.size) :
    Set.range (a.chart (V.val.gluingData.index i)) ⊆ V.locus :=
  (Set.subset_iUnion (fun t => Set.range (a.chart (V.val.gluingData.index t))) i).trans
    V.val.gluingData_locus.subset

variable (φ : ∀ k : a.Index, Set.range (a.chart k) ⊆ V.locus → BoundedAlgHom K R (a.algebra k))
  (hφ : V.IsChartCompatible φ)

/-- The given maps on the charts of the chosen special cover. -/
def gluingFamily (i : Fin V.val.gluingData.size) :
    BoundedAlgHom K R (a.algebra (V.val.gluingData.index i)) :=
  φ (V.val.gluingData.index i) (V.gluingIndex_subset i)

include hφ in
/-- Both maps to an actual overlap chart are the given map on that chart. -/
theorem gluingFamily_mapCompatible : V.val.gluingData.MapCompatible (V.gluingFamily φ) := by
  intro i j
  have hov : Set.range (a.chart (V.val.gluingData.overlap i j)) ⊆ V.locus :=
    (V.val.gluingData.overlap_subset_left i j).trans (V.gluingIndex_subset i)
  exact (hφ _ _ hov (V.gluingIndex_subset i) (V.val.gluingData.overlap_subset_left i j)).trans
    (hφ _ _ hov (V.gluingIndex_subset j) (V.val.gluingData.overlap_subset_right i j)).symm

/-- Bounded descent into the recognized algebra through its actual section
algebra. -/
def glue : BoundedAlgHom K R V.algebra :=
  V.property.algebraEquiv.symm.toBoundedAlgHom.comp
    (V.val.gluingData.lift (V.gluingFamily φ) (V.gluingFamily_mapCompatible φ hφ))

theorem algebraEquiv_comp_glue :
    V.property.algebraEquiv.toBoundedAlgHom.comp (V.glue φ hφ) =
      V.val.gluingData.lift (V.gluingFamily φ) (V.gluingFamily_mapCompatible φ hφ) :=
  BoundedAlgHom.ext fun _ => V.property.algebraEquiv.apply_symm_apply _

/-- The glued map recovers the given map on every contained original chart,
not only on the charts of the chosen special cover. -/
theorem originalRestriction_comp_glue (k : a.Index) (hk : Set.range (a.chart k) ⊆ V.locus) :
    (V.originalRestriction k hk).comp (V.glue φ hφ) = φ k hk := by
  let d := V.val.gluingData
  have hk' : Set.range (a.chart k) ⊆ d.locus := hk.trans V.val.gluingData_locus.symm.subset
  let c := d.subordinateCoverOfHausdorff k hk'
  have hmain : (d.originalRestriction k hk').comp
      (d.lift (V.gluingFamily φ) (V.gluingFamily_mapCompatible φ hφ)) = φ k hk := by
    apply BoundedAlgHom.ext
    intro r
    apply c.domainCover.algebra_ext_of_restrict_eq
    intro t
    have hct : Set.range (a.chart (c.index t)) ⊆ V.locus := (c.subset_parent t).trans hk
    have h1 := congrArg
      (fun q : BoundedAlgHom K d.SectionAlgebra (a.algebra (c.index t)) =>
        q (d.lift (V.gluingFamily φ) (V.gluingFamily_mapCompatible φ hφ) r))
      (d.original_comp_originalRestriction k hk' (c.index t) (c.subset_parent t)
        (c.member t) (c.subset_member t))
    have h2 := congrArg (fun q : BoundedAlgHom K R (a.algebra (c.index t)) => q r)
      (hφ (c.index t) (d.index (c.member t)) hct (V.gluingIndex_subset (c.member t))
        (c.subset_member t))
    have h3 := congrArg (fun q : BoundedAlgHom K R (a.algebra (c.index t)) => q r)
      (hφ (c.index t) k hct hk (c.subset_parent t))
    change a.restriction (c.index t) k (c.subset_parent t)
        (d.originalRestriction k hk'
          (d.lift (V.gluingFamily φ) (V.gluingFamily_mapCompatible φ hφ) r)) =
      a.restriction (c.index t) k (c.subset_parent t) (φ k hk r)
    exact h1.trans (h2.trans h3.symm)
  calc (V.originalRestriction k hk).comp (V.glue φ hφ)
      = (d.originalRestriction k hk').comp
          (V.property.algebraEquiv.toBoundedAlgHom.comp (V.glue φ hφ)) := rfl
    _ = φ k hk := by rw [V.algebraEquiv_comp_glue]; exact hmain

omit φ hφ in
/-- Bounded maps into a recognized algebra are detected by all canonical
original-chart restrictions. -/
theorem hom_ext {Ψ Ψ' : BoundedAlgHom K R V.algebra}
    (h : ∀ (k : a.Index) (hk : Set.range (a.chart k) ⊆ V.locus),
      (V.originalRestriction k hk).comp Ψ = (V.originalRestriction k hk).comp Ψ') :
    Ψ = Ψ' := by
  apply BoundedAlgHom.ext
  intro r
  apply V.componentCover.algebra_ext_of_restrict_eq
  intro i
  change (V.property.componentDomain i).baseMap (Ψ r) =
    (V.property.componentDomain i).baseMap (Ψ' r)
  rw [V.componentDomain_baseMap i]
  exact congrArg (fun q : BoundedAlgHom K R (a.algebra (V.property.cover.index i)) => q r)
    (h _ (V.component_subset i))

/-- The glued map is the only bounded map with the prescribed restrictions. -/
theorem eq_glue (Ψ : BoundedAlgHom K R V.algebra)
    (hΨ : ∀ (k : a.Index) (hk : Set.range (a.chart k) ⊆ V.locus),
      (V.originalRestriction k hk).comp Ψ = φ k hk) :
    Ψ = V.glue φ hφ :=
  V.hom_ext fun k hk => (hΨ k hk).trans (V.originalRestriction_comp_glue φ hφ k hk).symm

end IndexedAffinoidAtlas.RecognizedSubset

namespace AffinoidAtlasPresentation

/-- A continuous map with a compatible bounded algebra map for every
admissible chart pair. Unlike a strong map, no source chart is required to
map into some target chart. -/
structure AdmissiblePairSystem (A : AffinoidAtlasPresentation.{u, v, w} K)
    (B : AffinoidAtlasPresentation.{u, v', w'} K) where
  baseMap : C(A.space, B.space)
  pullback : ∀ i j,
    baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) →
      BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i)
  chart_comm : ∀ i j h (x : BanachSpectrum (A.atlas.algebra i)),
    B.atlas.chart j (BanachSpectrum.comap (pullback i j h).toBoundedRingHom x) =
      baseMap (A.atlas.chart i x)
  restriction_comm : ∀ i i' j j'
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j')),
    (A.atlas.restriction i i' hi).comp (pullback i' j' h') =
      (pullback i j h).comp (B.atlas.restriction j j' hj)

namespace AdmissiblePairSystem

variable {A : AffinoidAtlasPresentation.{u, v, w} K} {B : AffinoidAtlasPresentation.{u, v', w'} K}

theorem ext {p q : AdmissiblePairSystem A B} (hb : p.baseMap = q.baseMap)
    (hp : ∀ i j (h : p.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
      p.pullback i j h = q.pullback i j (hb ▸ h)) : p = q := by
  cases p with
  | mk pb pp pc pr =>
  cases q with
  | mk qb qp qc qr =>
  change pb = qb at hb
  subst hb
  have hpq : pp = qp := by
    funext i j h
    exact hp i j h
  subst hpq
  rfl

end AdmissiblePairSystem

namespace StrongHom

section Conversion

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Forget only the target-existence condition of a strong map. -/
def toAdmissiblePairSystem (f : StrongHom A B) : AdmissiblePairSystem A B where
  baseMap := f.baseMap
  pullback := f.pullback
  chart_comm := f.chart_comm
  restriction_comm := f.restriction_comm

end Conversion

end StrongHom

namespace AdmissiblePairSystem

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- A pair system in which every source chart has an admissible target is a
strong map with exactly the same bounded maps. -/
def toStrongHom (p : AdmissiblePairSystem A B)
    (ht : ∀ i, ∃ j, p.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    StrongHom A B where
  baseMap := p.baseMap
  target_exists := ht
  pullback := p.pullback
  chart_comm := p.chart_comm
  restriction_comm := p.restriction_comm

@[simp]
theorem toStrongHom_toAdmissiblePairSystem (p : AdmissiblePairSystem A B)
    (ht : ∀ i, ∃ j, p.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    (p.toStrongHom ht).toAdmissiblePairSystem = p := rfl

@[simp]
theorem _root_.Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.toAdmissiblePairSystem_toStrongHom
    (f : StrongHom A B) : f.toAdmissiblePairSystem.toStrongHom f.target_exists = f := rfl

end AdmissiblePairSystem

namespace StrongHom

section SourceExtension

variable {P Q : AffinoidAtlasPresentation.{u, v, w} K} (h : StrongHom P Q)

/-- Admissibility of a recognized source chart passes to all contained
original source charts. -/
theorem recognized_admissible (V : P.atlas.RecognizedSubset) (j : Q.atlas.Index)
    (hV : h.baseMap '' Set.range V.chart ⊆ Set.range (Q.atlas.chart j))
    (k : P.atlas.Index) (hk : Set.range (P.atlas.chart k) ⊆ V.locus) :
    h.baseMap '' Set.range (P.atlas.chart k) ⊆ Set.range (Q.atlas.chart j) := by
  refine (Set.image_mono ?_).trans hV
  rw [V.range_chart]
  exact hk

/-- The original bounded pullbacks on all source charts inside `V`. -/
def recognizedChartPullbacks (V : P.atlas.RecognizedSubset) (j : Q.atlas.Index)
    (hV : h.baseMap '' Set.range V.chart ⊆ Set.range (Q.atlas.chart j)) :
    ∀ k : P.atlas.Index, Set.range (P.atlas.chart k) ⊆ V.locus →
      BoundedAlgHom K (Q.atlas.algebra j) (P.atlas.algebra k) :=
  fun k hk => h.pullback k j (h.recognized_admissible V j hV k hk)

theorem recognizedChartPullbacks_compatible (V : P.atlas.RecognizedSubset) (j : Q.atlas.Index)
    (hV : h.baseMap '' Set.range V.chart ⊆ Set.range (Q.atlas.chart j)) :
    V.IsChartCompatible (h.recognizedChartPullbacks V j hV) := by
  intro k l hk hl hkl
  have hr := h.restriction_comm k l j j hkl Set.Subset.rfl
    (h.recognized_admissible V j hV k hk) (h.recognized_admissible V j hV l hl)
  rw [Q.atlas.restriction_id, BoundedAlgHom.comp_id] at hr
  exact hr

/-- Extend a strong map to all pairs of a recognized source subset and an
admissible original target chart, by bounded descent of the original pullbacks. -/
def recognizedSourceExtension : AdmissiblePairSystem P.recognitionPresentation Q where
  baseMap := h.baseMap
  pullback V j hV := RecognizedSubset.glue (a := P.atlas) V
    (h.recognizedChartPullbacks V j hV) (h.recognizedChartPullbacks_compatible V j hV)
  chart_comm V j hV x := by
    change P.atlas.RecognizedSubset at V
    change Q.atlas.chart j (BanachSpectrum.comap (V.glue (h.recognizedChartPullbacks V j hV)
      (h.recognizedChartPullbacks_compatible V j hV)).toBoundedRingHom x) = h.baseMap (V.chart x)
    have hx0 : V.chart x ∈ V.locus := by
      rw [← V.range_chart]
      exact Set.mem_range_self x
    have hx : V.chart x ∈ ⋃ i, Set.range (P.atlas.chart (V.val.gluingData.index i)) :=
      V.val.gluingData_locus.symm.subset hx0
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    have hk := V.gluingIndex_subset i
    have hxy : BanachSpectrum.comap (V.originalRestriction _ hk).toBoundedRingHom y = x :=
      V.isEmbedding_chart.injective ((V.chart_originalRestriction _ hk y).trans hy)
    subst hxy
    have hrec := V.originalRestriction_comp_glue (h.recognizedChartPullbacks V j hV)
      (h.recognizedChartPullbacks_compatible V j hV) _ hk
    calc Q.atlas.chart j (BanachSpectrum.comap (V.glue (h.recognizedChartPullbacks V j hV)
          (h.recognizedChartPullbacks_compatible V j hV)).toBoundedRingHom
          (BanachSpectrum.comap (V.originalRestriction _ hk).toBoundedRingHom y))
        = Q.atlas.chart j (BanachSpectrum.comap ((V.originalRestriction _ hk).comp
            (V.glue (h.recognizedChartPullbacks V j hV)
              (h.recognizedChartPullbacks_compatible V j hV))).toBoundedRingHom y) := rfl
      _ = Q.atlas.chart j (BanachSpectrum.comap
            (h.recognizedChartPullbacks V j hV _ hk).toBoundedRingHom y) := by rw [hrec]
      _ = h.baseMap (P.atlas.chart _ y) := h.chart_comm _ j _ y
      _ = h.baseMap (V.chart
            (BanachSpectrum.comap (V.originalRestriction _ hk).toBoundedRingHom y)) := by
          rw [V.chart_originalRestriction]
  restriction_comm U V j j' hUV hj hU hV := by
    change P.atlas.RecognizedSubset at U V
    have hUV' : U.locus ⊆ V.locus := by
      rw [← U.range_chart, ← V.range_chart]
      exact hUV
    change (U.restriction V hUV').comp (V.glue (h.recognizedChartPullbacks V j' hV)
        (h.recognizedChartPullbacks_compatible V j' hV)) =
      (U.glue (h.recognizedChartPullbacks U j hU)
        (h.recognizedChartPullbacks_compatible U j hU)).comp (Q.atlas.restriction j j' hj)
    apply U.hom_ext
    intro k hk
    calc (U.originalRestriction k hk).comp ((U.restriction V hUV').comp
          (V.glue (h.recognizedChartPullbacks V j' hV)
            (h.recognizedChartPullbacks_compatible V j' hV)))
        = (V.originalRestriction k (hk.trans hUV')).comp
            (V.glue (h.recognizedChartPullbacks V j' hV)
              (h.recognizedChartPullbacks_compatible V j' hV)) :=
          congrArg (fun q => BoundedAlgHom.comp q (V.glue (h.recognizedChartPullbacks V j' hV)
            (h.recognizedChartPullbacks_compatible V j' hV)))
            (U.originalRestriction_comp_restriction V hUV' k hk)
      _ = h.pullback k j' (h.recognized_admissible V j' hV k (hk.trans hUV')) :=
          V.originalRestriction_comp_glue _ _ k _
      _ = (h.pullback k j (h.recognized_admissible U j hU k hk)).comp
            (Q.atlas.restriction j j' hj) :=
          h.pullback_comp_restriction k j j' hj _ _
      _ = (U.originalRestriction k hk).comp ((U.glue (h.recognizedChartPullbacks U j hU)
            (h.recognizedChartPullbacks_compatible U j hU)).comp
              (Q.atlas.restriction j j' hj)) :=
          (congrArg (fun q => BoundedAlgHom.comp q (Q.atlas.restriction j j' hj))
            (U.originalRestriction_comp_glue (h.recognizedChartPullbacks U j hU)
              (h.recognizedChartPullbacks_compatible U j hU) k hk)).symm

@[simp]
theorem recognizedSourceExtension_baseMap :
    h.recognizedSourceExtension.baseMap = h.baseMap := rfl

/-- On every contained original chart, the extension restricts to the
unchanged original bounded pullback. -/
theorem originalRestriction_comp_recognizedSourceExtension (V : P.atlas.RecognizedSubset)
    (j : Q.atlas.Index) (hV : h.baseMap '' Set.range V.chart ⊆ Set.range (Q.atlas.chart j))
    (k : P.atlas.Index) (hk : Set.range (P.atlas.chart k) ⊆ V.locus) :
    (V.originalRestriction k hk).comp (h.recognizedSourceExtension.pullback V j hV) =
      h.pullback k j (h.recognized_admissible V j hV k hk) :=
  V.originalRestriction_comp_glue (h.recognizedChartPullbacks V j hV)
    (h.recognizedChartPullbacks_compatible V j hV) k hk

/-- Uniqueness: a pair system with the same ambient map and the same
original restrictions is the constructed extension. -/
theorem eq_recognizedSourceExtension (p : AdmissiblePairSystem P.recognitionPresentation Q)
    (hb : p.baseMap = h.baseMap)
    (hp : ∀ (V : P.atlas.RecognizedSubset) (j : Q.atlas.Index)
      (hV : p.baseMap '' Set.range V.chart ⊆ Set.range (Q.atlas.chart j))
      (k : P.atlas.Index) (hk : Set.range (P.atlas.chart k) ⊆ V.locus),
      (V.originalRestriction k hk).comp (p.pullback V j hV) =
        h.pullback k j (h.recognized_admissible V j (hb ▸ hV) k hk)) :
    p = h.recognizedSourceExtension := by
  apply AdmissiblePairSystem.ext hb
  intro V j hV
  change P.atlas.RecognizedSubset at V
  exact V.eq_glue (h.recognizedChartPullbacks V j (hb ▸ hV))
    (h.recognizedChartPullbacks_compatible V j (hb ▸ hV)) _ (hp V j hV)

end SourceExtension

section FullRecognition

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- A strong map of local-domain enlargements followed by the canonical
inclusion of the target enlargement into its full recognition. -/
def toFullRecognitionTarget (g : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    StrongHom A.saturatedPresentation B.fullRecognitionPresentation :=
  g.saturatedComp B.localDomainToFullRecognition A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains

@[simp]
theorem toFullRecognitionTarget_baseMap
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    g.toFullRecognitionTarget.baseMap = g.baseMap := rfl

/-- Through any intermediate target local domain inside `W`, the composite
pullback is the original pullback followed by the canonical restriction. -/
theorem toFullRecognitionTarget_pullback
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (S : A.atlas.saturatedAtlas.Index) (T : B.atlas.saturatedAtlas.Index)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (hST : g.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆
      Set.range (B.atlas.saturatedAtlas.chart T))
    (hTW : Set.range (B.atlas.saturatedAtlas.chart T) ⊆ W.locus)
    (hSW : g.toFullRecognitionTarget.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆
      Set.range (B.fullRecognitionPresentation.atlas.chart W)) :
    g.toFullRecognitionTarget.pullback S W hSW =
      (g.pullback S T hST).comp (W.originalRestriction T hTW) := by
  have hη : B.localDomainToFullRecognition.baseMap ''
      Set.range (B.saturatedPresentation.atlas.chart T) ⊆
        Set.range (B.fullRecognitionPresentation.atlas.chart W) := by
    change _root_.id '' Set.range (B.atlas.saturatedAtlas.chart T) ⊆ Set.range W.chart
    rw [Set.image_id, W.range_chart]
    exact hTW
  exact StrongHom.saturatedComp_pullback g B.localDomainToFullRecognition _ _ S T W hST hη hSW

/-- Berkovich's extension of a strong map to all pairs of recognized
affinoid subsets of the source and target full recognitions. -/
def fullRecognitionPairs (g : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    AdmissiblePairSystem A.fullRecognitionPresentation B.fullRecognitionPresentation :=
  g.toFullRecognitionTarget.recognizedSourceExtension

@[simp]
theorem fullRecognitionPairs_baseMap
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    g.fullRecognitionPairs.baseMap = g.baseMap := rfl

/-- The extended map on a pair `V`, `W` restricts to the original bounded
pullback on every contained source local domain `S` mapping into a contained
target local domain `T`. -/
theorem originalRestriction_comp_fullRecognitionPairs
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (hVW : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (S : A.atlas.saturatedAtlas.Index) (hS : Set.range (A.atlas.saturatedAtlas.chart S) ⊆ V.locus)
    (T : B.atlas.saturatedAtlas.Index) (hT : Set.range (B.atlas.saturatedAtlas.chart T) ⊆ W.locus)
    (hST : g.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆
      Set.range (B.atlas.saturatedAtlas.chart T)) :
    (V.originalRestriction S hS).comp (g.fullRecognitionPairs.pullback V W hVW) =
      (g.pullback S T hST).comp (W.originalRestriction T hT) :=
  (g.toFullRecognitionTarget.originalRestriction_comp_recognizedSourceExtension V W hVW S hS).trans
    (g.toFullRecognitionTarget_pullback S T W hST hT _)

/-- The identity of the local-domain enlargement extends to the identity
strong map of the full recognition atlas. -/
theorem fullRecognitionPairs_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    (StrongHom.id A.saturatedPresentation).fullRecognitionPairs =
      (StrongHom.id A.fullRecognitionPresentation).toAdmissiblePairSystem := by
  symm
  apply (StrongHom.id A.saturatedPresentation).toFullRecognitionTarget.eq_recognizedSourceExtension
    (StrongHom.id A.fullRecognitionPresentation).toAdmissiblePairSystem rfl
  intro V W hVW k hk
  change A.atlas.saturatedAtlas.RecognizedSubset at W
  have hVW' : V.locus ⊆ W.locus :=
    V.range_chart.symm.subset.trans
      (((Set.image_id (Set.range V.chart)).symm.subset.trans hVW).trans W.range_chart.subset)
  have hkk : (StrongHom.id A.saturatedPresentation).baseMap ''
      Set.range (A.atlas.saturatedAtlas.chart k) ⊆ Set.range (A.atlas.saturatedAtlas.chart k) :=
    (Set.image_id (Set.range (A.atlas.saturatedAtlas.chart k))).subset
  refine Eq.trans ?_ ((StrongHom.id A.saturatedPresentation).toFullRecognitionTarget_pullback
    k k W hkk (hk.trans hVW') _).symm
  have hid : (StrongHom.id A.saturatedPresentation).pullback k k hkk =
      BoundedAlgHom.id K (A.atlas.saturatedAtlas.algebra k) :=
    A.atlas.saturatedAtlas.restriction_id k Set.Subset.rfl
  exact (V.originalRestriction_comp_restriction W hVW' k hk).trans
    (congrArg (fun q => BoundedAlgHom.comp q (W.originalRestriction k (hk.trans hVW'))) hid).symm

/-- A coherent strong map of the original presentations, through its
constructed local-domain extension. -/
def fullRecognitionPairsOfCoherent (f : StrongHom A B) (hf : f.HasCoherentPullbacks) :
    AdmissiblePairSystem A.fullRecognitionPresentation B.fullRecognitionPresentation :=
  (f.saturationExtension hf).fullRecognitionPairs

@[simp]
theorem fullRecognitionPairsOfCoherent_baseMap (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks) :
    (f.fullRecognitionPairsOfCoherent hf).baseMap = f.baseMap := rfl

end FullRecognition

end StrongHom

end AffinoidAtlasPresentation

end Langlands.Analytic
