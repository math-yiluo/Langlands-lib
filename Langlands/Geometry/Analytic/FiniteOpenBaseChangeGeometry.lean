import Langlands.Geometry.Analytic.FiniteOpenBaseChangeModels
import Langlands.Geometry.Analytic.FibreProductChartSystem

/-! # Actual finite local models in the unrestricted product quotient -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R) (i : Fin M.rightCover.cover.size)

/-- The actual domain of the right cover, recognized with its original
bounded algebra equivalence. -/
abbrev rightRecognition : B.atlas.saturatedAtlas.RecognizedSubset :=
  g.domainRecognition R (M.rightCover.cover.obj i)

theorem rightRecognition_admissible :
    g.baseMap '' range (M.rightRecognition i).chart ⊆
      range (M.rightCover.target i).chart :=
  g.domainRecognition_admissible R (M.rightCover.cover.obj i) (M.rightCover.target i)
    (M.rightCover.image_subset_target i)

/-- Each local finite model supplies a literal original pair in the
canonical recognition-selected cospan. -/
def pairIndex : FibreProduct.PairIndex f.compatibleRecognitionMap g.compatibleRecognitionMap :=
  ⟨(f.recognitionSourceIndex (M.left i) (M.rightCover.target i) (M.left_admissible i),
      g.recognitionSourceIndex (M.rightRecognition i) (M.rightCover.target i)
        (M.rightRecognition_admissible i)),
    M.rightCover.target i, M.left_admissible i, M.rightRecognition_admissible i⟩

theorem pairCommonBase :
    FibreProduct.IsCommonBase f.compatibleRecognitionMap g.compatibleRecognitionMap
      (M.pairIndex i).val.1 (M.pairIndex i).val.2 (M.rightCover.target i) :=
  ⟨M.left_admissible i, M.rightRecognition_admissible i⟩

/-- The actual bounded algebra equivalence from the unchanged domain
algebra to its constructed recognized algebra. -/
abbrev rightRecognitionEquiv :
    BoundedAlgEquiv K (M.rightCover.cover.obj i).algebra (M.rightRecognition i).algebra :=
  g.domainRecognitionEquiv R (M.rightCover.cover.obj i)

theorem rightRecognitionEquiv_comp_canonicalPullback :
    (M.rightRecognitionEquiv i).toBoundedAlgHom.comp (M.rightCover.canonicalPullback i) =
      g.fullRecognitionPairs.pullback (M.rightRecognition i) (M.rightCover.target i)
        (M.rightRecognition_admissible i) := by
  apply BoundedAlgHom.ext
  intro x
  exact (M.rightRecognitionEquiv i).apply_symm_apply _

/-- Map the chosen-base original pair algebra to the actual local model,
retaining the full first leg and the transported full second leg. -/
def pairToModel :
    BoundedAlgHom K
      (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
      (M.algebra i) :=
  AffinoidPushout.lift _ _ (M.algebra i) (M.leftMap i)
    ((M.rightMap i).comp (M.rightRecognitionEquiv i).symm.toBoundedAlgHom)
    (FibreProduct.condition_of_isCommonBase (M.pairCommonBase i)
      (FibreProduct.isCommonBase_base _ _ (M.pairIndex i)) _ _ (M.condition i))

theorem pairToModel_comp_leftMap :
    (M.pairToModel i).comp
      (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =
      M.leftMap i :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem pairToModel_comp_rightMap :
    (M.pairToModel i).comp
      (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =
      (M.rightMap i).comp (M.rightRecognitionEquiv i).symm.toBoundedAlgHom :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

/-- The inverse uses the original pair legs and the forward constructed
recognition equivalence. -/
def modelToPair :
    BoundedAlgHom K (M.algebra i)
      (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) :=
  AffinoidPushout.lift _ _ _ (FibreProduct.leftMap _ _ (M.pairIndex i))
    ((FibreProduct.rightMap _ _ (M.pairIndex i)).comp
      (M.rightRecognitionEquiv i).toBoundedAlgHom) (by
        apply BoundedAlgHom.ext
        intro x
        have h := congrArg (fun q : BoundedAlgHom K (M.rightCover.target i).algebra
          (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =>
            q x) (FibreProduct.condition _ _ (M.pairIndex i) (M.pairCommonBase i))
        exact h.trans (congrArg
          (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
          (congrArg (fun q : BoundedAlgHom K (M.rightCover.target i).algebra
            (M.rightRecognition i).algebra => q x)
              (M.rightRecognitionEquiv_comp_canonicalPullback i)).symm))

theorem modelToPair_comp_leftMap :
    (M.modelToPair i).comp (M.leftMap i) =
      FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i) :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem modelToPair_comp_rightMap :
    (M.modelToPair i).comp (M.rightMap i) =
      (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)).comp
        (M.rightRecognitionEquiv i).toBoundedAlgHom :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

theorem modelToPair_comp_pairToModel :
    (M.modelToPair i).comp (M.pairToModel i) =
      BoundedAlgHom.id K
        (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) := by
  apply AffinoidPushout.hom_ext
  · apply BoundedAlgHom.ext
    intro x
    exact (congrArg (M.modelToPair i)
      (congrArg (fun q : BoundedAlgHom K (M.left i).algebra (M.algebra i) => q x)
        (M.pairToModel_comp_leftMap i))).trans
      (congrArg (fun q : BoundedAlgHom K (M.left i).algebra
        (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =>
          q x) (M.modelToPair_comp_leftMap i))
  · apply BoundedAlgHom.ext
    intro x
    exact (congrArg (M.modelToPair i)
      (congrArg (fun q : BoundedAlgHom K (M.rightRecognition i).algebra (M.algebra i) => q x)
        (M.pairToModel_comp_rightMap i))).trans
      ((congrArg (fun q : BoundedAlgHom K (M.rightCover.cover.obj i).algebra
        (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =>
          q ((M.rightRecognitionEquiv i).symm x)) (M.modelToPair_comp_rightMap i)).trans
        (congrArg
          (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
          ((M.rightRecognitionEquiv i).apply_symm_apply x)))

theorem pairToModel_comp_modelToPair :
    (M.pairToModel i).comp (M.modelToPair i) = BoundedAlgHom.id K (M.algebra i) := by
  apply AffinoidPushout.hom_ext (M.leftBase i) (M.rightCover.canonicalPullback i)
  · apply BoundedAlgHom.ext
    intro x
    exact (congrArg (M.pairToModel i)
      (congrArg (fun q : BoundedAlgHom K (M.left i).algebra
        (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =>
          q x) (M.modelToPair_comp_leftMap i))).trans
      (congrArg (fun q : BoundedAlgHom K (M.left i).algebra (M.algebra i) => q x)
        (M.pairToModel_comp_leftMap i))
  · apply BoundedAlgHom.ext
    intro x
    exact (congrArg (M.pairToModel i)
      (congrArg (fun q : BoundedAlgHom K (M.rightCover.cover.obj i).algebra
        (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =>
          q x) (M.modelToPair_comp_rightMap i))).trans
      ((congrArg (fun q : BoundedAlgHom K (M.rightRecognition i).algebra (M.algebra i) =>
        q ((M.rightRecognitionEquiv i) x)) (M.pairToModel_comp_rightMap i)).trans
          (congrArg (M.rightMap i) ((M.rightRecognitionEquiv i).symm_apply_apply x)))

/-- A constructed whole bounded equivalence, rather than identification by
the action on spectrum points. -/
def pairAlgebraEquiv :
    BoundedAlgEquiv K
      (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
      (M.algebra i) :=
  BoundedAlgEquiv.ofHomInv (M.pairToModel i) (M.modelToPair i)
    (fun x => congrArg (fun q => q x) (M.modelToPair_comp_pairToModel i))
    (fun x => congrArg (fun q => q x) (M.pairToModel_comp_modelToPair i))

/-- The original local-model spectrum maps to the actual unrestricted
product quotient via the constructed whole algebra equivalence. -/
def productChart :
    C(BanachSpectrum (M.algebra i),
      (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space) where
  toFun x := (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).chart
    (M.pairIndex i) ((M.pairAlgebraEquiv i).spectrumHomeomorph x)
  continuous_toFun :=
    ((FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).continuous_chart
      (M.pairIndex i)).comp (M.pairAlgebraEquiv i).spectrumHomeomorph.continuous

theorem productChart_injective : Function.Injective (M.productChart i) :=
  ((FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).chart_injective
    (M.pairIndex i)).comp (M.pairAlgebraEquiv i).spectrumHomeomorph.injective

/-- The entire first leg identifies the actual first projection. -/
theorem fst_productChart (x : BanachSpectrum (M.algebra i)) :
    FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap (M.productChart i x) =
      (M.left i).chart (BanachSpectrum.comap (M.leftMap i).toBoundedRingHom x) := by
  exact congrArg (M.left i).chart
    (congrArg (fun q : BoundedAlgHom K (M.left i).algebra (M.algebra i) =>
      BanachSpectrum.comap q.toBoundedRingHom x) (M.pairToModel_comp_leftMap i))

/-- The entire second leg and the original domain-recognition equivalence
identify the actual second projection in the original ambient space. -/
theorem snd_productChart (x : BanachSpectrum (M.algebra i)) :
    FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap (M.productChart i x) =
      R.chart ((M.rightCover.cover.obj i).spectrumMap
        (BanachSpectrum.comap (M.rightMap i).toBoundedRingHom x)) := by
  let L : LocalDomain B.atlas.fullRecognitionAtlas := ⟨R, M.rightCover.cover.obj i⟩
  let t := FibreProduct.rightPoint f.compatibleRecognitionMap g.compatibleRecognitionMap
    (M.pairIndex i) ((M.pairAlgebraEquiv i).spectrumHomeomorph x)
  have he : (M.rightRecognitionEquiv i).spectrumHomeomorph t =
      BanachSpectrum.comap (M.rightMap i).toBoundedRingHom x := by
    apply BanachSpectrum.ext
    intro y
    exact (congrArg x (congrArg
      (fun q : BoundedAlgHom K (M.rightRecognition i).algebra (M.algebra i) =>
        q ((M.rightRecognitionEquiv i) y)) (M.pairToModel_comp_rightMap i))).trans
      (congrArg (fun z => x ((M.rightMap i) z))
        ((M.rightRecognitionEquiv i).symm_apply_apply y))
  exact (B.atlas.fullRecognitionLocalDomainAlgebraEquiv_chart L t).trans
    (congrArg L.ambientMap he)

/-- A given point of the actual product quotient lies in a local finite
model exactly when its projections satisfy the prescribed original loci.
This asserts chart membership, not injectivity of pairs of projections. -/
theorem mem_range_productChart_iff
    (z : (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space) :
    z ∈ range (M.productChart i) ↔
      FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap z ∈ V ∧
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap z ∈
        R.chart '' (M.rightCover.cover.obj i).locus := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(M.fst_productChart i x).symm ▸ M.leftPoint_mem i x, ?_⟩
    refine (M.snd_productChart i x).symm ▸ ⟨_, ?_, rfl⟩
    exact (M.rightCover.cover.obj i).represents.2.1.subset ⟨_, rfl⟩
  · rintro ⟨hzV, hzR⟩
    let π₁ := FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap
    have hzW : f.baseMap
        (π₁ z) ∈
        (M.rightCover.target i).locus :=
      (FibreProduct.baseMap_fst f.compatibleRecognitionMap g.compatibleRecognitionMap z).symm ▸
        (M.rightCover.image_subset_target i) ⟨_, hzR, rfl⟩
    have hzP : FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap z ∈
        (M.left i).locus := (M.left_locus i).symm.subset ⟨hzV, hzW⟩
    have hzpair : z ∈ range
        ((FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).chart
          (M.pairIndex i)) :=
      (FibreProduct.mem_range_chart_iff _ _ (M.pairIndex i) z).2
        ⟨(M.left i).range_chart.symm.subset hzP,
          (M.rightRecognition i).range_chart.symm.subset hzR⟩
    obtain ⟨t, ht⟩ := hzpair
    exact ⟨(M.pairAlgebraEquiv i).spectrumHomeomorph.symm t,
      (congrArg
        ((FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).chart
          (M.pairIndex i))
        ((M.pairAlgebraEquiv i).spectrumHomeomorph.apply_symm_apply t)).trans ht⟩

theorem range_productChart :
    range (M.productChart i) =
      FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹'
        (R.chart '' (M.rightCover.cover.obj i).locus) := by
  ext z
  exact M.mem_range_productChart_iff i z

/-- The finite family covers the literal prescribed preimage in the
actual quotient, including all product spectrum points over a point pair. -/
theorem iUnion_range_productChart :
    (⋃ i, range (M.productChart i)) =
      FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    obtain ⟨hV, y, -, hy⟩ := (M.mem_range_productChart_iff i z).1 hi
    exact ⟨hV, R.range_chart.subset ⟨y, hy⟩⟩
  · rintro ⟨hzV, hzR⟩
    obtain ⟨y, hy⟩ := R.range_chart.symm.subset hzR
    obtain ⟨i, hi⟩ := M.rightCover.cover.covers y (mem_univ y)
    exact mem_iUnion.2 ⟨i, (M.mem_range_productChart_iff i z).2 ⟨hzV, y, hi, hy⟩⟩

include M in
/-- The whole preimage is compact before any affinoid parent is supplied
and without a global Hausdorff assumption. -/
theorem isCompact_preimage :
    IsCompact
      (FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
        FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus) :=
  (iUnion_range_productChart M) ▸ isCompact_iUnion
    (fun i => isCompact_range (M.productChart i).continuous)

/-- Each unchanged local model maps into the literal whole finite
preimage, without an assumed presentation of that preimage. -/
def productPreimageChart :
    C(BanachSpectrum (M.algebra i),
      ↥(FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
        FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus)) where
  toFun x := ⟨M.productChart i x,
    (iUnion_range_productChart M).subset (mem_iUnion.2 ⟨i, x, rfl⟩)⟩
  continuous_toFun := (M.productChart i).continuous.subtype_mk _

/-- Separation is needed only on this actual preimage, for example when
it is contained in a Hausdorff open product patch. -/
theorem isClosedEmbedding_productPreimageChart
    [T2Space
      ↥(FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
        FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus)] :
    IsClosedEmbedding (M.productPreimageChart i) :=
  (M.productPreimageChart i).continuous.isClosedEmbedding
    (fun _ _ h => M.productChart_injective i (congrArg Subtype.val h))

theorem isEmbedding_productChart_of_t2Preimage
    [T2Space
      ↥(FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
        FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus)] :
    IsEmbedding (M.productChart i) :=
  IsEmbedding.subtypeVal.comp (M.isClosedEmbedding_productPreimageChart i).isEmbedding

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels
