import Langlands.Geometry.Analytic.FibreProductSmallAtlas
import Langlands.Geometry.Analytic.FibreProductPairDomains
import Langlands.Geometry.Analytic.LocalDomainSaturatedTransport
import Langlands.Geometry.Analytic.RecognitionFibreProductSmallness
import Langlands.Geometry.Analytic.AffinoidPointwiseBaseChange
import Langlands.Geometry.Analytic.QuasiIsoSourceEtale

/-! # Recognized original pair charts in the canonical small product -/

noncomputable section

universe u v

namespace Langlands.Analytic.FibreProduct

open CategoryTheory Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-- The entire first leg is retained by the change of common base. -/
theorem commonBaseAlgebraEquiv_comp_left (p : PairIndex f g) (k : C.atlas.Index)
    (hk : IsCommonBase f g p.1.1 p.1.2 k) :
    (commonBaseAlgebraEquiv f g p k hk).toBoundedAlgHom.comp (leftMap f g p) =
      AffinoidPushout.leftMap (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2) :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _
    (condition_of_isCommonBase hk (isCommonBase_base f g p) _ _
      (AffinoidPushout.condition (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)))

/-- The entire second leg is retained by the change of common base. -/
theorem commonBaseAlgebraEquiv_comp_right (p : PairIndex f g) (k : C.atlas.Index)
    (hk : IsCommonBase f g p.1.1 p.1.2 k) :
    (commonBaseAlgebraEquiv f g p k hk).toBoundedAlgHom.comp (rightMap f g p) =
      AffinoidPushout.rightMap (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2) :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _
    (condition_of_isCommonBase hk (isCommonBase_base f g p) _ _
      (AffinoidPushout.condition (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)))

variable [Small.{v} (chartSystem f g).Space] [Nonempty (LocalAtlasIndex f g)]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains) (p : PairIndex f g) (hp : p ∈ goodPairs f g)

/-- The whole original pair domain becomes an actual canonical small
saturated index, including an empty pair image. -/
def smallGoodPairIndex : (smallAtlas f g hA hB hC).saturatedAtlas.Index :=
  LocalDomain.transportedSaturatedIndex (localAtlas f g hA hB hC)
    (Shrink.homeomorph (chartSystem f g).Space) (equivShrink (LocalAtlasIndex f g)).symm
    (goodPairLocalDomain f g hA hB hC p hp)

/-- Intrinsic recognition of the transported actual whole pair domain.
No effective global algebra parent is needed for this single domain. -/
def smallGoodPairRecognition : (smallAtlas f g hA hB hC).saturatedAtlas.RecognizedSubset :=
  (smallAtlas f g hA hB hC).saturatedAtlas.originalRecognitionIndex
    (smallGoodPairIndex f g hA hB hC p hp)

/-- Every coefficient of the original raw pair algebra is retained. -/
def smallGoodPairEquiv : BoundedAlgEquiv K (algebra f g p)
    (smallGoodPairRecognition f g hA hB hC p hp).algebra :=
  (LocalDomain.transportedSaturatedEquiv (localAtlas f g hA hB hC)
    (Shrink.homeomorph (chartSystem f g).Space) (equivShrink (LocalAtlasIndex f g)).symm
    (goodPairLocalDomain f g hA hB hC p hp)).trans
      ((smallAtlas f g hA hB hC).saturatedAtlas.originalRecognitionAlgebraEquiv
        (smallGoodPairIndex f g hA hB hC p hp))

theorem smallGoodPairRecognition_locus :
    (smallGoodPairRecognition f g hA hB hC p hp).locus =
      (Shrink.homeomorph (chartSystem f g).Space) '' range ((chartSystem f g).chart p) :=
  (smallGoodPairRecognition f g hA hB hC p hp).range_chart.symm.trans
    (((smallAtlas f g hA hB hC).saturatedAtlas.recognitionAtlas_original_range
      (smallGoodPairIndex f g hA hB hC p hp)).trans
      ((LocalDomain.range_transportedSaturatedIndex (localAtlas f g hA hB hC)
        (Shrink.homeomorph (chartSystem f g).Space) (equivShrink (LocalAtlasIndex f g)).symm
        (goodPairLocalDomain f g hA hB hC p hp)).trans
          (congrArg (fun T => (Shrink.homeomorph (chartSystem f g).Space) '' T)
            (goodPairLocalDomain_locus f g hA hB hC p hp))))

theorem smallGoodPairEquiv_chart
    (x : BanachSpectrum (smallGoodPairRecognition f g hA hB hC p hp).algebra) :
    (smallGoodPairRecognition f g hA hB hC p hp).chart x =
      Shrink.homeomorph (chartSystem f g).Space
        ((chartSystem f g).chart p ((smallGoodPairEquiv f g hA hB hC p hp).spectrumHomeomorph x)) := by
  have h := LocalDomain.transportedSaturatedEquiv_chart (localAtlas f g hA hB hC)
    (Shrink.homeomorph (chartSystem f g).Space) (equivShrink (LocalAtlasIndex f g)).symm
    (goodPairLocalDomain f g hA hB hC p hp)
    (((smallAtlas f g hA hB hC).saturatedAtlas.originalRecognitionAlgebraEquiv
      (smallGoodPairIndex f g hA hB hC p hp)).spectrumHomeomorph x)
  exact ((smallAtlas f g hA hB hC).saturatedAtlas.recognitionAtlas_original_chart
    (smallGoodPairIndex f g hA hB hC p hp) x).trans
      (h.symm.trans (congrArg (Shrink.homeomorph (chartSystem f g).Space)
        (goodPairLocalDomain_ambientMap f g hA hB hC p hp _)))

/-- The complete second structural map into the actual small recognized chart. -/
def smallGoodPairRightMap : BoundedAlgHom K (B.atlas.algebra p.1.2)
    (smallGoodPairRecognition f g hA hB hC p hp).algebra :=
  (smallGoodPairEquiv f g hA hB hC p hp).toBoundedAlgHom.comp (rightMap f g p)

/-- Use any actual common base chart for the whole pair algebra, retaining
both complete original legs in the recognized chart. -/
def smallGoodPairCommonBaseEquiv (k : C.atlas.Index)
    (hk : IsCommonBase f g p.1.1 p.1.2 k) :
    BoundedAlgEquiv K
      (AffinoidPushout.algebra (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2))
      (smallGoodPairRecognition f g hA hB hC p hp).algebra :=
  (commonBaseAlgebraEquiv f g p k hk).symm.trans
    (smallGoodPairEquiv f g hA hB hC p hp)

theorem smallGoodPairCommonBaseEquiv_comp_right (k : C.atlas.Index)
    (hk : IsCommonBase f g p.1.1 p.1.2 k) :
    (smallGoodPairCommonBaseEquiv f g hA hB hC p hp k hk).toBoundedAlgHom.comp
      (AffinoidPushout.rightMap (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)) =
        smallGoodPairRightMap f g hA hB hC p hp := by
  apply BoundedAlgHom.ext
  intro x
  change (smallGoodPairEquiv f g hA hB hC p hp)
    ((commonBaseAlgebraEquiv f g p k hk).symm
      (AffinoidPushout.rightMap (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2) x)) = _
  have he := congrArg (fun q : BoundedAlgHom K (B.atlas.algebra p.1.2)
    (AffinoidPushout.algebra (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)) => q x)
    (commonBaseAlgebraEquiv_comp_right f g p k hk)
  exact congrArg (smallGoodPairEquiv f g hA hB hC p hp)
    ((congrArg (commonBaseAlgebraEquiv f g p k hk).symm he).symm.trans
      ((commonBaseAlgebraEquiv f g p k hk).symm_apply_apply _))

theorem smallGoodPairCommonBaseEquiv_comp_left (k : C.atlas.Index)
    (hk : IsCommonBase f g p.1.1 p.1.2 k) :
    (smallGoodPairCommonBaseEquiv f g hA hB hC p hp k hk).toBoundedAlgHom.comp
      (AffinoidPushout.leftMap (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)) =
        (smallGoodPairEquiv f g hA hB hC p hp).toBoundedAlgHom.comp (leftMap f g p) := by
  apply BoundedAlgHom.ext
  intro x
  change (smallGoodPairEquiv f g hA hB hC p hp)
    ((commonBaseAlgebraEquiv f g p k hk).symm
      (AffinoidPushout.leftMap (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2) x)) = _
  have he := congrArg (fun q : BoundedAlgHom K (A.atlas.algebra p.1.1)
    (AffinoidPushout.algebra (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)) => q x)
    (commonBaseAlgebraEquiv_comp_left f g p k hk)
  exact congrArg (smallGoodPairEquiv f g hA hB hC p hp)
    ((congrArg (commonBaseAlgebraEquiv f g p k hk).symm he).symm.trans
      ((commonBaseAlgebraEquiv f g p k hk).symm_apply_apply _))

/-- Finite Banachness at any actual common base passes to the original
complete second map in the canonical small recognized pair chart. -/
theorem smallGoodPairRightMap_isFiniteBanach
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) (k : C.atlas.Index)
    (hk : IsCommonBase f g p.1.1 p.1.2 k)
    (hf : (f.pullback p.1.1 k hk.1).IsFiniteBanach) :
    (smallGoodPairRightMap f g hA hB hC p hp).IsFiniteBanach :=
  (smallGoodPairCommonBaseEquiv_comp_right f g hA hB hC p hp k hk) ▸
    ((smallGoodPairCommonBaseEquiv f g hA hB hC p hp k hk).isFiniteBanach.comp
      (hpush _ _ _ _ _ hf))

/-- The original full tensor base change gives pointwise etaleness of
the complete second map in the actual small recognized pair chart. -/
theorem smallGoodPairRightMap_isEtaleAtPoint
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (k : C.atlas.Index) (hk : IsCommonBase f g p.1.1 p.1.2 k)
    (hf : (f.pullback p.1.1 k hk.1).IsFiniteBanach)
    (x : BanachSpectrum (smallGoodPairRecognition f g hA hB hC p hp).algebra)
    (hx : (f.pullback p.1.1 k hk.1).IsEtaleAtPoint
      (leftPoint f g p ((smallGoodPairEquiv f g hA hB hC p hp).spectrumHomeomorph x))) :
    (smallGoodPairRightMap f g hA hB hC p hp).IsEtaleAtPoint x := by
  let e := smallGoodPairCommonBaseEquiv f g hA hB hC p hp k hk
  have hleft := congrArg (fun q : BoundedAlgHom K (A.atlas.algebra p.1.1)
    (smallGoodPairRecognition f g hA hB hC p hp).algebra =>
      BanachSpectrum.comap q.toBoundedRingHom x)
    (smallGoodPairCommonBaseEquiv_comp_left f g hA hB hC p hp k hk)
  have hx' : (f.pullback p.1.1 k hk.1).IsEtaleAtPoint
      (BanachSpectrum.comap
        (AffinoidPushout.leftMap (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)).toBoundedRingHom
        (e.spectrumHomeomorph x)) := hleft.symm ▸ hx
  have hr := AffinoidPushout.rightMap_isEtaleAtPoint_of_tensorComparison
    (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)
    (htensor _ _ _ _ _ hf) hf.finite.finiteType (e.spectrumHomeomorph x) hx'
  have he := (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
    e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint x
  have hcomp : (e.toBoundedAlgHom.comp
      (AffinoidPushout.rightMap (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2))).IsEtaleAtPoint x :=
    ⟨he.1.comp hr.1, BoundedAlgHom.IsUnramifiedAtPoint.comp
      e.isFiniteBanach.finite.finiteType (hpush _ _ _ _ _ hf).finite.finiteType he.2 hr.2⟩
  exact (smallGoodPairCommonBaseEquiv_comp_right f g hA hB hC p hp k hk) ▸ hcomp

end Langlands.Analytic.FibreProduct
