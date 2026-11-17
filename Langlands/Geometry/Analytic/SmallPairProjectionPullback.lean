import Langlands.Geometry.Analytic.SmallFibreProductPairRecognition
import Langlands.Geometry.Analytic.SmallFibreProductProjectionCoefficients
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion

/-! # Actual full-recognition pullbacks on small pair charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Singleton recognition's bounded comparison is inverse to the complete
original-chart restriction, including every nonreduced coefficient. -/
theorem originalRestriction_comp_originalRecognitionAlgebraEquiv (i : a.Index)
    (hi : range (a.chart i) ⊆ (a.originalRecognitionIndex i).locus) :
    ((a.originalRecognitionIndex i).originalRestriction i hi).comp
      (a.originalRecognitionAlgebraEquiv i).toBoundedAlgHom = BoundedAlgHom.id K (a.algebra i) := by
  let V : a.RecognizedSubset := a.originalRecognitionIndex i
  let d := V.val.gluingData
  let hd : d.locus = range (a.chart i) := V.val.gluingData_locus
  have hcomp : (V.originalRestriction i hi).comp (a.originalRecognitionAlgebraEquiv i).toBoundedAlgHom =
      (d.originalRestriction i (hi.trans V.val.gluingData_locus.symm.subset)).comp
        (SpecialSubset.originalAlgebraEquiv a i).toBoundedAlgHom := by
    apply BoundedAlgHom.ext
    intro x
    change d.originalRestriction i _
      (V.property.algebraEquiv (V.property.algebraEquiv.symm
        ((SpecialSubset.originalAlgebraEquiv a i) x))) = _
    exact congrArg (d.originalRestriction i (hi.trans V.val.gluingData_locus.symm.subset))
      (V.property.algebraEquiv.apply_symm_apply ((SpecialSubset.originalAlgebraEquiv a i) x))
  apply hcomp.trans
  apply BoundedAlgHom.ext
  intro x
  apply (d.parentDomainCover i hd).algebra_ext_of_restrict_eq
  intro j
  have hres := d.original_comp_originalRestriction i
    (hi.trans V.val.gluingData_locus.symm.subset) (d.index j)
    (d.member_subset_parent i hd j) j Subset.rfl
  have hres' := hres.trans
    ((congrArg (fun q : BoundedAlgHom K (a.algebra (d.index j)) (a.algebra (d.index j)) =>
      q.comp (d.projection j)) (a.restriction_id (d.index j) Subset.rfl)).trans
        (BoundedAlgHom.id_comp _))
  exact congrArg (fun q : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index j)) =>
    q ((SpecialSubset.originalAlgebraEquiv a i) x)) hres' 

end Langlands.Analytic.IndexedAffinoidAtlas

namespace Langlands.Analytic.FibreProduct

open CategoryTheory Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  [Small.{v} (chartSystem f g).Space] [Nonempty (LocalAtlasIndex f g)]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains) (p : PairIndex f g) (hp : p ∈ goodPairs f g)

omit [Small.{v} (chartSystem f g).Space] in
/-- The original right leg satisfies the entire target coefficient law
relative to its actual containing raw product chart. -/
theorem goodPairLocalDomain_right_change :
    B.atlas.IsMapChartChange
      (goodPairLocalDomain f g hA hB hC p hp).index.rep.1.2 p.1.2 (algebra f g p)
      ((goodPairLocalDomain f g hA hB hC p hp).domain.baseMap.comp
        (rightMap f g (goodPairLocalDomain f g hA hB hC p hp).index.rep))
      (rightMap f g p) := by
  let h := range_subset_goodPairContainer f g p hp
  have hc := B.atlas.changeMapChart_reverse_isMapChartChange p.1.2
    (goodPairContainer f g p hp).rep.1.2 (algebra f g p) (rightMap f g p)
    (rightPoint_mem_of_range_subset h)
  exact (rangeRestriction_comp_rightMap f g h).symm ▸ hc

/-- The complete small projection maps the entire pair chart into its
original right chart, also on the chosen saturated representatives. -/
theorem smallGoodPair_saturated_admissible :
    (smallSndHom f g hA hB hC).baseMap ''
      range ((smallAtlas f g hA hB hC).saturatedAtlas.chart
        (smallGoodPairIndex f g hA hB hC p hp)) ⊆
      range (B.atlas.saturatedAtlas.chart
        ⟨(B.atlas.originalLocalDomain p.1.2).locus, ⟨B.atlas.originalLocalDomain p.1.2, rfl⟩⟩) := by
  have hraw : snd f g '' range ((chartSystem f g).chart p) ⊆ range (B.atlas.chart p.1.2) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨rightPoint f g p x, rfl⟩
  have hL := (LocalDomain.range_transportedSaturatedIndex (localAtlas f g hA hB hC)
    (Shrink.homeomorph (chartSystem f g).Space) (equivShrink (LocalAtlasIndex f g)).symm
    (goodPairLocalDomain f g hA hB hC p hp)).trans
      (congrArg (fun S => (Shrink.homeomorph (chartSystem f g).Space) '' S)
        (goodPairLocalDomain_locus f g hA hB hC p hp))
  exact (image_mono hL.subset).trans ((smallSndBase_image_shrink f g hA hB hC hraw).trans
    ((B.atlas.originalLocalDomain_locus p.1.2).symm.subset.trans
      (B.atlas.range_saturatedChart
        ⟨(B.atlas.originalLocalDomain p.1.2).locus, ⟨B.atlas.originalLocalDomain p.1.2, rfl⟩⟩).symm.subset))

/-- The entire second projection on a transported original raw pair
retains exactly its original right bounded leg through saturation. -/
theorem smallGoodPair_saturation_pullback :
    let V := B.atlas.originalLocalDomain p.1.2
    let q := smallSndHom f g hA hB hC
    ((q.saturationExtension).pullback (smallGoodPairIndex f g hA hB hC p hp)
      ⟨V.locus, ⟨V, rfl⟩⟩ (smallGoodPair_saturated_admissible f g hA hB hC p hp)).comp
      (B.atlas.localDomainSaturatedEquiv V).toBoundedAlgHom =
    (LocalDomain.transportedSaturatedEquiv (localAtlas f g hA hB hC)
      (Shrink.homeomorph (chartSystem f g).Space) (equivShrink (LocalAtlasIndex f g)).symm
      (goodPairLocalDomain f g hA hB hC p hp)).toBoundedAlgHom.comp (rightMap f g p) := by
  let U := goodPairLocalDomain f g hA hB hC p hp
  let V := B.atlas.originalLocalDomain p.1.2
  have h : snd f g '' U.locus ⊆ V.locus := by
    rw [goodPairLocalDomain_locus f g hA hB hC p hp, B.atlas.originalLocalDomain_locus]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨rightPoint f g p x, rfl⟩
  exact smallSnd_saturation_pullback_of_factor_change f g hA hB hC U V (rightMap f g p) h
    (goodPairLocalDomain_right_change f g hA hB hC p hp)

/-- The actual full-recognition pair of the small second projection is
admissible on the entire recognized raw pair image. -/
theorem smallGoodPair_recognized_admissible :
    (smallSndHom f g hA hB hC).saturationExtension.baseMap ''
      range (smallGoodPairRecognition f g hA hB hC p hp).chart ⊆
      range (B.atlas.recognizedLocalDomain (B.atlas.originalLocalDomain p.1.2)).chart :=
  (image_mono ((smallAtlas f g hA hB hC).saturatedAtlas.recognitionAtlas_original_range
    (smallGoodPairIndex f g hA hB hC p hp)).subset).trans
      ((smallGoodPair_saturated_admissible f g hA hB hC p hp).trans
        (B.atlas.saturatedAtlas.recognitionAtlas_original_range
          ⟨(B.atlas.originalLocalDomain p.1.2).locus, ⟨B.atlas.originalLocalDomain p.1.2, rfl⟩⟩).symm.subset)

/-- The existing full-recognition pair pullback of the actual small
second saturation projection on the two specified recognized charts. -/
abbrev smallGoodPairFullPullback : BoundedAlgHom K
    (B.atlas.recognizedLocalDomain (B.atlas.originalLocalDomain p.1.2)).algebra
    (smallGoodPairRecognition f g hA hB hC p hp).algebra :=
  ((smallSndHom f g hA hB hC).saturationExtension.fullRecognitionPairs).pullback
    (smallGoodPairRecognition f g hA hB hC p hp)
    (B.atlas.recognizedLocalDomain (B.atlas.originalLocalDomain p.1.2))
    (smallGoodPair_recognized_admissible f g hA hB hC p hp)

/-- The ACTUAL full-recognition pair pullback, expressed on the unchanged
original right chart algebra. -/
def smallGoodPairActualRightMap : BoundedAlgHom K (B.atlas.algebra p.1.2)
    (smallGoodPairRecognition f g hA hB hC p hp).algebra :=
  (((smallSndHom f g hA hB hC).saturationExtension.fullRecognitionPairs).pullback
    (smallGoodPairRecognition f g hA hB hC p hp)
    (B.atlas.recognizedLocalDomain (B.atlas.originalLocalDomain p.1.2))
    (smallGoodPair_recognized_admissible f g hA hB hC p hp)).comp
      (B.atlas.recognizedLocalDomainAlgebraEquiv (B.atlas.originalLocalDomain p.1.2)).toBoundedAlgHom

/-- The complete actual full-recognition pullback is exactly the original
right coefficient map transported to the recognized small pair algebra. -/
theorem smallGoodPairActualRightMap_eq :
    smallGoodPairActualRightMap f g hA hB hC p hp =
      smallGoodPairRightMap f g hA hB hC p hp := by
  let a := smallAtlas f g hA hB hC
  let U := goodPairLocalDomain f g hA hB hC p hp
  let V := B.atlas.originalLocalDomain p.1.2
  let S := smallGoodPairIndex f g hA hB hC p hp
  let T : B.atlas.saturatedAtlas.Index := ⟨V.locus, ⟨V, rfl⟩⟩
  let P := smallGoodPairRecognition f g hA hB hC p hp
  let R := B.atlas.recognizedLocalDomain V
  let q := (smallSndHom f g hA hB hC).saturationExtension
  let hS := a.saturatedAtlas.originalRecognitionIndex_range_subset S
  let hT := B.atlas.saturatedAtlas.originalRecognitionIndex_range_subset T
  let ρS := P.originalRestriction S hS
  let ρT := R.originalRestriction T hT
  let E := LocalDomain.transportedSaturatedEquiv (localAtlas f g hA hB hC)
    (Shrink.homeomorph (chartSystem f g).Space) (equivShrink (LocalAtlasIndex f g)).symm U
  have hs := a.saturatedAtlas.originalRestriction_comp_originalRecognitionAlgebraEquiv S hS
  have ht := B.atlas.saturatedAtlas.originalRestriction_comp_originalRecognitionAlgebraEquiv T hT
  have hse : ρS.comp (smallGoodPairEquiv f g hA hB hC p hp).toBoundedAlgHom = E.toBoundedAlgHom := by
    apply BoundedAlgHom.ext
    intro x
    exact congrArg (fun z : BoundedAlgHom K (a.saturatedAtlas.algebra S)
      (a.saturatedAtlas.algebra S) => z (E x)) hs
  have hte : ρT.comp (B.atlas.recognizedLocalDomainAlgebraEquiv V).toBoundedAlgHom =
      (B.atlas.localDomainSaturatedEquiv V).toBoundedAlgHom := by
    apply BoundedAlgHom.ext
    intro x
    exact congrArg (fun z : BoundedAlgHom K (B.atlas.saturatedAtlas.algebra T)
      (B.atlas.saturatedAtlas.algebra T) => z ((B.atlas.localDomainSaturatedEquiv V) x)) ht
  have hn := q.originalRestriction_comp_fullRecognitionPairs P R
    (smallGoodPair_recognized_admissible f g hA hB hC p hp) S hS T hT
    (smallGoodPair_saturated_admissible f g hA hB hC p hp)
  have hsat := smallGoodPair_saturation_pullback f g hA hB hC p hp
  apply BoundedAlgHom.ext
  intro x
  apply (a.saturatedAtlas.originalRecognitionRestrictionEquiv S).injective
  change ρS (smallGoodPairActualRightMap f g hA hB hC p hp x) =
    ρS (smallGoodPairRightMap f g hA hB hC p hp x)
  exact (congrArg (fun z : BoundedAlgHom K R.algebra (a.saturatedAtlas.algebra S) =>
    z ((B.atlas.recognizedLocalDomainAlgebraEquiv V) x)) hn).trans
      ((congrArg (q.pullback S T (smallGoodPair_saturated_admissible f g hA hB hC p hp))
        (congrArg (fun z : BoundedAlgHom K V.algebra (B.atlas.saturatedAtlas.algebra T) => z x) hte)).trans
          ((congrArg (fun z : BoundedAlgHom K V.algebra (a.saturatedAtlas.algebra S) => z x) hsat).trans
            (congrArg (fun z : BoundedAlgHom K (algebra f g p) (a.saturatedAtlas.algebra S) =>
              z (rightMap f g p x)) hse).symm))

/-- The unchanged original target algebra and its entire recognition
comparison recover the actual full-recognition pair map. -/
theorem smallGoodPairFullPullback_eq :
    smallGoodPairFullPullback f g hA hB hC p hp =
      (smallGoodPairRightMap f g hA hB hC p hp).comp
        (B.atlas.recognizedLocalDomainAlgebraEquiv
          (B.atlas.originalLocalDomain p.1.2)).symm.toBoundedAlgHom := by
  let e := B.atlas.recognizedLocalDomainAlgebraEquiv (B.atlas.originalLocalDomain p.1.2)
  apply BoundedAlgHom.ext
  intro x
  have he := congrArg (fun z : BoundedAlgHom K (B.atlas.algebra p.1.2)
    (smallGoodPairRecognition f g hA hB hC p hp).algebra => z (e.symm x))
    (smallGoodPairActualRightMap_eq f g hA hB hC p hp)
  exact (congrArg (smallGoodPairFullPullback f g hA hB hC p hp)
    (e.apply_symm_apply x)).symm.trans he

/-- The ACTUAL full-recognition second projection map is finite Banach
whenever the first original pair map is finite over any common base. -/
theorem smallGoodPairFullPullback_isFiniteBanach
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) (k : C.atlas.Index)
    (hk : IsCommonBase f g p.1.1 p.1.2 k)
    (hf : (f.pullback p.1.1 k hk.1).IsFiniteBanach) :
    (smallGoodPairFullPullback f g hA hB hC p hp).IsFiniteBanach :=
  (smallGoodPairFullPullback_eq f g hA hB hC p hp).symm ▸
    ((smallGoodPairRightMap_isFiniteBanach f g hA hB hC p hp hpush k hk hf).comp
      (B.atlas.recognizedLocalDomainAlgebraEquiv (B.atlas.originalLocalDomain p.1.2)).symm.isFiniteBanach)

/-- Pointwise etaleness under the full tensor comparison holds for the
existing entire full-recognition second projection map itself. -/
theorem smallGoodPairFullPullback_isEtaleAtPoint
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (k : C.atlas.Index) (hk : IsCommonBase f g p.1.1 p.1.2 k)
    (hf : (f.pullback p.1.1 k hk.1).IsFiniteBanach)
    (x : BanachSpectrum (smallGoodPairRecognition f g hA hB hC p hp).algebra)
    (hx : (f.pullback p.1.1 k hk.1).IsEtaleAtPoint
      (leftPoint f g p ((smallGoodPairEquiv f g hA hB hC p hp).spectrumHomeomorph x))) :
    (smallGoodPairFullPullback f g hA hB hC p hp).IsEtaleAtPoint x := by
  let e := B.atlas.recognizedLocalDomainAlgebraEquiv (B.atlas.originalLocalDomain p.1.2)
  let r := smallGoodPairRightMap f g hA hB hC p hp
  have hr := smallGoodPairRightMap_isEtaleAtPoint f g hA hB hC p hp hpush htensor k hk hf x hx
  have he := (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
    e.symm.toBoundedAlgHom e.symm.toAlgEquiv.bijective).isEtaleAtPoint
      (BanachSpectrum.comap r.toBoundedRingHom x)
  have hcomp : (r.comp e.symm.toBoundedAlgHom).IsEtaleAtPoint x :=
    ⟨hr.1.comp he.1, BoundedAlgHom.IsUnramifiedAtPoint.comp
      (smallGoodPairRightMap_isFiniteBanach f g hA hB hC p hp hpush k hk hf).finite.finiteType
      e.symm.isFiniteBanach.finite.finiteType hr.2 he.2⟩
  exact (smallGoodPairFullPullback_eq f g hA hB hC p hp).symm ▸ hcomp

end Langlands.Analytic.FibreProduct
