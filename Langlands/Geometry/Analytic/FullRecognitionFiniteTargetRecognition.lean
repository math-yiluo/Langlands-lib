import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetChartBinding
import Langlands.Geometry.Analytic.SmallFiniteOpenRecognition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation

/-! # Recognized finite preimages from effective target-local descent -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas.RecognizedSubset

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- Bounded maps into a recognized algebra are detected by the original
restrictions to charts lying in some member of a finite recognized cover. -/
theorem hom_ext_of_finiteCover (V : a.RecognizedSubset) {n : ℕ}
    (Y : Fin n → a.RecognizedSubset) (hY : ∀ k, (Y k).locus ⊆ V.locus)
    (hcov : V.locus ⊆ ⋃ k, (Y k).locus)
    {R : Type z} [NormedCommRing R] [Algebra K R] {Ψ Ψ' : BoundedAlgHom K R V.algebra}
    (h : ∀ k (s : a.Index) (hs : range (a.chart s) ⊆ (Y k).locus),
      (V.originalRestriction s (hs.trans (hY k))).comp Ψ =
        (V.originalRestriction s (hs.trans (hY k))).comp Ψ') :
    Ψ = Ψ' := by
  let D (k : Fin n) : Domain K V.algebra :=
    ⟨(Y k).algebra, (Y k).restriction V (hY k), V.chart ⁻¹' (Y k).locus,
      (Y k).restriction_represents V (hY k)⟩
  let c : Domain.FiniteCover (Domain.whole K V.algebra) :=
    { size := n
      obj := D
      map := fun k => ⟨(D k).baseMap, rfl⟩
      covers := fun x _ => by
        have hx : V.chart x ∈ V.locus := V.range_chart ▸ mem_range_self x
        obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hx)
        exact ⟨k, hk⟩ }
  apply BoundedAlgHom.ext
  intro r
  apply c.algebra_ext_of_restrict_eq
  intro k
  have hk : ((Y k).restriction V (hY k)).comp Ψ = ((Y k).restriction V (hY k)).comp Ψ' := by
    apply (Y k).hom_ext
    intro s hs
    rw [← BoundedAlgHom.comp_assoc, ← BoundedAlgHom.comp_assoc,
      (Y k).originalRestriction_comp_restriction V (hY k) s hs]
    exact h k s hs
  exact congrArg (fun q : BoundedAlgHom K R (Y k).algebra => q r) hk

end Langlands.Analytic.IndexedAffinoidAtlas.RecognizedSubset

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FamilyRefinement

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas
open FiniteAffinoidAlgebraDescent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {V : Set A.space} {U : Set B.space} {W : B.atlas.saturatedAtlas.RecognizedSubset}
  (F : g.FamilyRefinement V U W)

theorem iUnion_range_modelChart :
    ⋃ k, range (F.modelChart k) = V ∩ g.baseMap ⁻¹' W.locus := by
  ext z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    obtain ⟨hzV, hzk⟩ := (F.mem_range_modelChart k z).1 hk
    exact ⟨hzV, F.index_subset_locus k ((F.piece_eq k).subset hzk)⟩
  · rintro ⟨hzV, hzW⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (F.covers hzW)
    exact mem_iUnion.mpr ⟨k, (F.mem_range_modelChart k z).2 ⟨hzV, (F.piece_eq k).symm.subset hk⟩⟩

theorem chartBinding_locus_eq :
    F.chartBinding.gluingData.locus = V ∩ g.baseMap ⁻¹' W.locus :=
  F.chartBinding_locus.trans F.iUnion_range_modelChart

/-- Hausdorffness of the literal preimage is all the recognition needs. -/
theorem chartBinding_t2 [hT : T2Space ↥(V ∩ g.baseMap ⁻¹' W.locus)] :
    T2Space F.chartBinding.gluingData.locus :=
  F.chartBinding_locus_eq.symm ▸ hT

/-! ### The canonical target maps are the original restrictions -/

/-- The canonical bounded target map of a refinement chart is the original
restriction of its family member to that chart. -/
theorem canonicalPullback_eq (k : Fin F.size) :
    F.models.rightCover.canonicalPullback k =
      (F.target k).originalRestriction (F.index k) (F.index_subset_target k) := by
  let aB := B.atlas.fullRecognitionAtlas
  let D := F.domain k
  let L : LocalDomain aB := ⟨W, D⟩
  let Xr := (StrongHom.id B.saturatedPresentation).domainRecognition W D
  let eD := (StrongHom.id B.saturatedPresentation).domainRecognitionEquiv W D
  have hXl : Xr.locus = range (B.atlas.saturatedAtlas.chart (F.index k)) := F.piece_eq k
  have hXi : range (B.atlas.saturatedAtlas.chart (F.index k)) ⊆ Xr.locus := hXl.symm.subset
  have hXW : Xr.locus ⊆ W.locus := hXl.subset.trans (F.index_subset_locus k)
  have hXT : Xr.locus ⊆ (F.target k).locus := hXl.subset.trans (F.index_subset_target k)
  have hX : (StrongHom.id B.saturatedPresentation).baseMap '' range Xr.chart ⊆
      range (F.target k).chart :=
    (StrongHom.id B.saturatedPresentation).domainRecognition_admissible W D (F.target k)
      (F.models.rightCover.image_subset_target k)
  -- the identity pair pullback is the recognized restriction
  have hpull : (StrongHom.id B.saturatedPresentation).fullRecognitionPairs.pullback Xr
      (F.target k) hX = Xr.restriction (F.target k) hXT := by
    rw [AdmissiblePairSystem.pullback_congr (fullRecognitionPairs_id B) Xr (F.target k) hX hX]
    rfl
  -- the recognition comparison composed with the domain map is a restriction
  let f : L ⟶ aB.originalLocalDomain W :=
    (LocalDomain.sameChartFunctor aB W).map
      (show D ⟶ Domain.whole K W.algebra from ⟨D.baseMap, BoundedAlgHom.comp_id _⟩)
  let j : aB.originalLocalDomain Xr ⟶ L := (B.atlas.fullRecognitionLocalDomainUnitIso.app L).inv
  have h1 : eD.toBoundedAlgHom.comp D.baseMap = Xr.restriction W hXW := by
    have h := aB.originalLocalDomain_restriction Xr W
      (Xr.range_chart.subset.trans (hXW.trans W.range_chart.symm.subset)) (j ≫ f)
    exact h
  have h2 := Xr.originalRestriction_comp_restriction W hXW (F.index k) hXi
  have h3 : (Xr.originalRestriction (F.index k) hXi).comp eD.toBoundedAlgHom =
      BoundedAlgHom.id K D.algebra := by
    apply D.represents.hom_ext D.algebra
    have e1 := congrArg (fun q => (Xr.originalRestriction (F.index k) hXi).comp q) h1
    exact e1.trans h2
  have h4 : eD.symm.toBoundedAlgHom = Xr.originalRestriction (F.index k) hXi := by
    apply BoundedAlgHom.ext
    intro x
    have := congrArg (fun q : BoundedAlgHom K D.algebra D.algebra => q (eD.symm x)) h3
    change Xr.originalRestriction (F.index k) hXi (eD (eD.symm x)) = eD.symm x at this
    rw [eD.apply_symm_apply] at this
    exact this.symm
  change eD.symm.toBoundedAlgHom.comp
      ((StrongHom.id B.saturatedPresentation).fullRecognitionPairs.pullback Xr (F.target k) hX) = _
  rw [hpull, h4]
  exact Xr.originalRestriction_comp_restriction (F.target k) hXT (F.index k) hXi

/-! ### Restriction from a local model to an original chart -/

theorem range_modelChart_subset_left (k : Fin F.size) :
    range (F.modelChart k) ⊆ (F.left k).locus := by
  rw [F.range_modelChart k, F.left_locus k]
  exact fun z hz => ⟨hz.1, F.piece_subset_target k hz.2⟩

theorem originalLocalDomain_subset_model (k : Fin F.size) (s : A.atlas.saturatedAtlas.Index)
    (hs : range (A.atlas.saturatedAtlas.chart s) ⊆ range (F.modelChart k)) :
    (A.atlas.saturatedAtlas.recognitionOriginalLocalDomain s).locus ⊆
      (F.modelDomain k).locus := by
  rw [A.atlas.saturatedAtlas.recognitionOriginalLocalDomain_locus s, F.modelDomain_locus k]
  exact hs

/-- The bounded restriction from a local model to an original saturated
chart contained in its ambient range, as the thin local-domain arrow. -/
def modelRestriction (k : Fin F.size) (s : A.atlas.saturatedAtlas.Index)
    (hs : range (A.atlas.saturatedAtlas.chart s) ⊆ range (F.modelChart k)) :
    BoundedAlgHom K (F.models.algebra k) (A.atlas.saturatedAtlas.algebra s) :=
  (A.atlas.saturatedAtlas.recognitionOriginalDomain s).baseMap.comp
    (show A.atlas.saturatedAtlas.recognitionOriginalLocalDomain s ⟶ F.modelDomain k from
      LocalDomain.Inclusion.ofSubset _ _ (F.originalLocalDomain_subset_model k s hs)).restriction

/-- On the finite left preimage, model restriction recovers the original
restriction of the family member's recognized preimage. -/
theorem modelRestriction_leftMap (k : Fin F.size) (s : A.atlas.saturatedAtlas.Index)
    (hs : range (A.atlas.saturatedAtlas.chart s) ⊆ range (F.modelChart k)) :
    (F.modelRestriction k s hs).comp (F.models.leftMap k) =
      (F.left k).originalRestriction s (hs.trans (F.range_modelChart_subset_left k)) := by
  let a' := A.atlas.fullRecognitionAtlas
  let O := A.atlas.saturatedAtlas.originalRecognitionIndex s
  let r : A.atlas.saturatedAtlas.recognitionOriginalLocalDomain s ⟶ F.modelDomain k :=
    LocalDomain.Inclusion.ofSubset _ _ (F.originalLocalDomain_subset_model k s hs)
  let ι : F.modelDomain k ⟶ a'.originalLocalDomain (F.left k) :=
    (LocalDomain.sameChartFunctor a' (F.left k)).map
      (show (F.leftDomain k).extend (Domain.whole K (F.models.algebra k)) ⟶
          Domain.whole K (F.left k).algebra from
        ⟨F.models.leftMap k, BoundedAlgHom.comp_id _⟩)
  have h' : O.locus ⊆ (F.left k).locus :=
    (O.range_chart.symm.trans (A.atlas.saturatedAtlas.recognitionAtlas_original_range s)).subset.trans
      (hs.trans (F.range_modelChart_subset_left k))
  have hO : range (a'.chart O) ⊆ range (a'.chart (F.left k)) :=
    O.range_chart.subset.trans (h'.trans (F.left k).range_chart.symm.subset)
  have h1 : (r ≫ ι).restriction = O.restriction (F.left k) h' :=
    a'.originalLocalDomain_restriction O (F.left k) hO (r ≫ ι)
  have h2 := O.originalRestriction_comp_restriction (F.left k) h' s Subset.rfl
  exact (congrArg (fun q => BoundedAlgHom.comp
    (A.atlas.saturatedAtlas.recognitionOriginalDomain s).baseMap q) h1).trans h2

/-- On the right cover member, model restriction is the original pair
pullback, by cancelling the representing canonical target map. -/
theorem modelRestriction_rightMap (k : Fin F.size) (s : A.atlas.saturatedAtlas.Index)
    (hs : range (A.atlas.saturatedAtlas.chart s) ⊆ range (F.modelChart k))
    (hST : g.baseMap '' range (A.atlas.saturatedAtlas.chart s) ⊆
      range (B.atlas.saturatedAtlas.chart (F.index k))) :
    (F.modelRestriction k s hs).comp (F.models.rightMap k) = g.pullback s (F.index k) hST := by
  apply (F.canonicalPullback_represents k).hom_ext (A.atlas.saturatedAtlas.algebra s)
  have hc := F.models.condition k
  have hl := F.modelRestriction_leftMap k s hs
  have hp := originalRestriction_comp_fullRecognitionPairs g (F.left k) (F.target k)
    (F.left_admissible k) s (hs.trans (F.range_modelChart_subset_left k)) (F.index k)
    (F.index_subset_target k) hST
  have hC := F.canonicalPullback_eq k
  have s2 := congrArg (fun q => BoundedAlgHom.comp (F.modelRestriction k s hs) q) hc.symm
  have s4 := congrArg (fun q => BoundedAlgHom.comp q (F.models.leftBase k)) hl
  have s6 := congrArg (fun q => BoundedAlgHom.comp (g.pullback s (F.index k) hST) q) hC.symm
  exact s2.trans (s4.trans (hp.trans s6))

/-- Model restriction is also the composite through the saturated model
chart and the canonical saturated representative of the original chart. -/
theorem modelRestriction_eq (k : Fin F.size) (s : A.atlas.saturatedAtlas.Index)
    (hs : range (A.atlas.saturatedAtlas.chart s) ⊆ range (F.modelChart k))
    (h : range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart
        (A.atlas.saturatedAtlas.recognitionOriginalSaturatedIndex s)) ⊆
      range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart (F.modelIndex k))) :
    ((A.atlas.saturatedAtlas.recognitionOriginalDomain s).baseMap.comp
        (A.atlas.saturatedAtlas.recognitionOriginalToSaturated s).restriction).comp
      ((A.atlas.fullRecognitionAtlas.saturatedAtlas.restriction
          (A.atlas.saturatedAtlas.recognitionOriginalSaturatedIndex s) (F.modelIndex k) h).comp
        (F.modelEquiv k).toBoundedAlgHom) =
      F.modelRestriction k s hs := by
  let a' := A.atlas.fullRecognitionAtlas
  let U : LocalDomain a' := A.atlas.saturatedAtlas.recognitionOriginalLocalDomain s
  let r : U ⟶ F.modelDomain k :=
    LocalDomain.Inclusion.ofSubset _ _ (F.originalLocalDomain_subset_model k s hs)
  have hn := a'.localDomainSaturatedEquiv_naturality U (F.modelDomain k) r h
  let e := LocalDomain.isoOfLocusEq U
    (a'.saturatedRepresentative (A.atlas.saturatedAtlas.recognitionOriginalSaturatedIndex s))
    (a'.saturatedRepresentative_locus
      (A.atlas.saturatedAtlas.recognitionOriginalSaturatedIndex s)).symm
  have hid : A.atlas.saturatedAtlas.recognitionOriginalToSaturated s ≫ e.inv = 𝟙 U :=
    @Subsingleton.elim (LocalDomain.Inclusion U U) inferInstance _ _
  have hid' := congrArg LocalDomain.Inclusion.restriction hid
  have e1 := congrArg (fun q => BoundedAlgHom.comp
    ((A.atlas.saturatedAtlas.recognitionOriginalDomain s).baseMap.comp
      (A.atlas.saturatedAtlas.recognitionOriginalToSaturated s).restriction) q) hn
  have e2 := congrArg (fun q => BoundedAlgHom.comp
    (A.atlas.saturatedAtlas.recognitionOriginalDomain s).baseMap
      (BoundedAlgHom.comp q r.restriction)) hid'
  exact e1.trans e2

/-! ### The recognized finite preimage -/

section Recognition

variable [T2Space ↥(V ∩ g.baseMap ⁻¹' W.locus)]
  (P : EffectiveRealization F.models.algebraDescentData)

/-- An effective realization of the local descent datum recognizes the
literal finite union of the model charts in the recognized source atlas. -/
def recognizedPreimage : A.atlas.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset :=
  letI := F.chartBinding_t2
  F.chartBinding.recognizedSubset P

theorem recognizedPreimage_locus :
    (F.recognizedPreimage P).locus = V ∩ g.baseMap ⁻¹' W.locus :=
  F.chartBinding_locus_eq

/-- The whole effective parent algebra is retained in the recognized preimage. -/
def recognitionEquiv : BoundedAlgEquiv K P.algebra (F.recognizedPreimage P).algebra :=
  letI := F.chartBinding_t2
  F.chartBinding.recognitionEquiv P

/-- The finite bounded structural map from the target affinoid. -/
def finiteBaseMap : BoundedAlgHom K W.algebra (F.recognizedPreimage P).algebra :=
  (F.recognitionEquiv P).toBoundedAlgHom.comp P.toMatchingPresentation.baseMap

theorem finiteBaseMap_isFiniteBanach : (F.finiteBaseMap P).IsFiniteBanach :=
  (F.recognitionEquiv P).isFiniteBanach.comp P.finite

theorem modelIndex_subset (k : Fin F.size) :
    range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart (F.modelIndex k)) ⊆
      (F.recognizedPreimage P).locus :=
  fun _ hx => mem_iUnion.mpr ⟨k, hx⟩

/-- On every model chart, the finite structural map is the model's right
leg after the original restriction of the target affinoid. -/
theorem finiteBaseMap_originalRestriction (k : Fin F.size)
    (hk : range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart (F.modelIndex k)) ⊆
      (F.recognizedPreimage P).locus) :
    ((F.recognizedPreimage P).originalRestriction (F.modelIndex k) hk).comp
        (F.finiteBaseMap P) =
      (F.modelEquiv k).toBoundedAlgHom.comp
        ((F.models.rightMap k).comp (F.models.rightCover.cover.obj k).baseMap) := by
  let _ := F.chartBinding_t2
  have he := (F.chartBinding.affinoidRealization P).originalRestriction_comp_recognitionEquiv
    k hk
  have hs : (P.toMatchingPresentation.localMap k).comp P.toMatchingPresentation.baseMap =
      (F.models.rightMap k).comp (F.models.rightCover.cover.obj k).baseMap :=
    (P.toMatchingPresentation.localMap_baseMap k).trans
      (F.models.descentLocalAlgebras.structuralMap_eq k)
  exact (congrArg (fun q => BoundedAlgHom.comp q P.toMatchingPresentation.baseMap) he).trans
    (congrArg (fun q => BoundedAlgHom.comp (F.modelEquiv k).toBoundedAlgHom q) hs)

/-- The recognized preimage in the original saturated atlas, by recognition
idempotence. -/
def preimage : A.atlas.saturatedAtlas.RecognizedSubset :=
  A.atlas.fullRecognitionIdempotenceIndex (F.recognizedPreimage P)

theorem preimage_locus : (F.preimage P).locus = V ∩ g.baseMap ⁻¹' W.locus :=
  F.recognizedPreimage_locus P

theorem preimage_admissible :
    g.baseMap '' range (F.preimage P).chart ⊆ range W.chart := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ V ∩ g.baseMap ⁻¹' W.locus :=
    (F.preimage_locus P).subset ((F.preimage P).range_chart.subset hz)
  exact W.range_chart.symm.subset hz'.2

/-- The finite structural map into the recognized preimage. -/
def preimageMap : BoundedAlgHom K W.algebra (F.preimage P).algebra :=
  (A.atlas.fullRecognitionIdempotenceAlgebraEquiv (F.recognizedPreimage P)).toBoundedAlgHom.comp
    (F.finiteBaseMap P)

theorem preimageMap_isFiniteBanach : (F.preimageMap P).IsFiniteBanach :=
  (A.atlas.fullRecognitionIdempotenceAlgebraEquiv (F.recognizedPreimage P)).isFiniteBanach.comp
    (F.finiteBaseMap_isFiniteBanach P)

/-- The actual full-recognition pair pullback over the recognized preimage
is the finite structural map. -/
theorem pullback_eq :
    g.fullRecognitionPairs.pullback (F.preimage P) W (F.preimage_admissible P) =
      F.preimageMap P := by
  let Z := F.recognizedPreimage P
  let b' := A.atlas.fullRecognitionAtlas.saturatedAtlas
  let Y : Fin F.size → A.atlas.saturatedAtlas.RecognizedSubset := fun k =>
    A.atlas.fullRecognitionLocalDomainFunctor.obj (F.modelDomain k)
  have hYl : ∀ k, (Y k).locus = range (F.modelChart k) := fun k => F.modelDomain_locus k
  have hY : ∀ k, (Y k).locus ⊆ (F.preimage P).locus := fun k => by
    rw [hYl k, F.preimage_locus P, ← F.iUnion_range_modelChart]
    exact subset_iUnion (fun j => range (F.modelChart j)) k
  have hcov : (F.preimage P).locus ⊆ ⋃ k, (Y k).locus := by
    rw [F.preimage_locus P, ← F.iUnion_range_modelChart]
    exact iUnion_mono fun k => (hYl k).symm.subset
  refine RecognizedSubset.hom_ext_of_finiteCover (F.preimage P) Y hY hcov ?_
  intro k s hs
  have hsm : range (A.atlas.saturatedAtlas.chart s) ⊆ range (F.modelChart k) :=
    hs.trans (hYl k).subset
  have hST : g.baseMap '' range (A.atlas.saturatedAtlas.chart s) ⊆
      range (B.atlas.saturatedAtlas.chart (F.index k)) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (F.piece_eq k).subset ((F.mem_range_modelChart k z).1 (hsm hz)).2
  have hsZ : range (A.atlas.saturatedAtlas.chart s) ⊆ Z.locus := hs.trans (hY k)
  let S' := A.atlas.saturatedAtlas.recognitionOriginalSaturatedIndex s
  have hS'Z : range (b'.chart S') ⊆ Z.locus :=
    (A.atlas.saturatedAtlas.recognitionOriginalSaturatedIndex_range s).subset.trans hsZ
  have hk := F.modelIndex_subset P k
  have hS'k : range (b'.chart S') ⊆ range (b'.chart (F.modelIndex k)) :=
    (A.atlas.saturatedAtlas.recognitionOriginalSaturatedIndex_range s).subset.trans
      (hsm.trans (F.range_modelIndex k).symm.subset)
  let pS := (A.atlas.saturatedAtlas.recognitionOriginalDomain s).baseMap.comp
    (A.atlas.saturatedAtlas.recognitionOriginalToSaturated s).restriction
  have hL := originalRestriction_comp_fullRecognitionPairs g (F.preimage P) W
    (F.preimage_admissible P) s (hs.trans (hY k)) (F.index k) (F.index_subset_locus k) hST
  have hI := A.atlas.fullRecognitionIdempotenceAlgebraEquiv_originalRestriction Z s hsZ
  have hN := Z.originalRestriction_naturality (F.modelIndex k) S' hk hS'Z hS'k
  have hB := F.finiteBaseMap_originalRestriction P k hk
  have hM := F.modelRestriction_eq k s hsm hS'k
  have hR := F.modelRestriction_rightMap k s hsm hST
  refine hL.trans ?_
  symm
  have t2 := congrArg (fun q => BoundedAlgHom.comp q (F.finiteBaseMap P)) hI
  have t4 := congrArg (fun q => BoundedAlgHom.comp (BoundedAlgHom.comp pS q) (F.finiteBaseMap P))
    hN.symm
  have t6 := congrArg (fun q => BoundedAlgHom.comp
    (pS.comp (b'.restriction S' (F.modelIndex k) hS'k)) q) hB
  have t8 := congrArg (fun q => BoundedAlgHom.comp (BoundedAlgHom.comp q (F.models.rightMap k))
    (F.models.rightCover.cover.obj k).baseMap) hM
  have t9 := congrArg (fun q => BoundedAlgHom.comp q (F.models.rightCover.cover.obj k).baseMap) hR
  exact t2.trans (t4.trans (t6.trans (t8.trans t9)))

theorem pullback_isFiniteBanach :
    (g.fullRecognitionPairs.pullback (F.preimage P) W (F.preimage_admissible P)).IsFiniteBanach := by
  rw [F.pullback_eq P]
  exact F.preimageMap_isFiniteBanach P

end Recognition

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FamilyRefinement
