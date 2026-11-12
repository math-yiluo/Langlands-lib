import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionOpenSubspaces

/-! # Source restrictions over fixed target dimension strata -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open TopologicalSpace Topology
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.AlgebraicGeometry

/-- On a locally Noetherian smooth source, the actual constant local fibre
 dimension determines the standard smooth relative dimension. -/
theorem smoothOfRelativeDimension_of_localDimension
    {U V : Scheme.{u}} [IsLocallyNoetherian U] (f : U ⟶ V)
    (hf : Smooth f) (n : ℕ)
    (hd : ∀ x : U, relativeTopologicalKrullDimAt f x = (n : WithBot ℕ∞)) :
    SmoothOfRelativeDimension n f := by
  let := hf
  apply IsZariskiLocalAtSource.of_openCover
    (P := @SmoothOfRelativeDimension.{u} n) (componentOpenCover U)
  intro i
  obtain ⟨m, hm⟩ := smoothConnectedRelativeDimension
    (componentScheme U i) V (componentι U i ≫ f) (by infer_instance) inferInstance
  let z : componentScheme U i := Classical.arbitrary _
  have hlocal := (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq
    (componentι U i ≫ f) m).mp (smoothPureDimension.2 _ _ _ m hm) z
  have he : (m : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
    hlocal.symm.trans ((relativeTopologicalKrullDimAt_etale_source
      (componentι U i) f z).trans (hd _))
  have hmn : m = n := by exact_mod_cast he
  exact hmn ▸ hm

namespace AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

namespace PointOpenSubspace

/-- A representable open inclusion is also etale. -/
theorem isEtale_of_isOpenImmersion {F G : Presheaf S} {i : F ⟶ G}
    (hi : IsOpenImmersion i) : IsEtale i := by
  apply MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (Over.forget S)) ?_ i hi
  intro U V p hp
  let : _root_.AlgebraicGeometry.IsOpenImmersion p.left := hp
  exact inferInstanceAs (Etale p.left)

end PointOpenSubspace

namespace SmoothTargetPointDimensions

variable (d : SmoothTargetPointDimensions f)

/-- The actual source locus lying over one target dimension stratum. -/
def sourceSubfunctor (n : ℕ) : Subfunctor X.presheaf :=
  (PointOpenSubspace.subfunctor Y.presheaf (d.targetSubset n)).preimage (hom f)

theorem sourceSubfunctor_isOpenImmersion (n : ℕ) :
    IsOpenImmersion (d.sourceSubfunctor n).ι := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (Over.forget S))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S))
    (AffineOpenSubfunctors.isPullback_fromPreimage
      (PointOpenSubspace.subfunctor Y.presheaf (d.targetSubset n)) (hom f))
    (d.targetInclusion_isOpenImmersion n)

/-- The actual open algebraic subspace of source points over dimension `n`. -/
def sourceSpace (n : ℕ) : AlgebraicSpace S :=
  OpenSubspaceGeometry.openSubspace X (d.sourceSubfunctor n)
    (d.sourceSubfunctor_isOpenImmersion n)

def sourceInclusion (n : ℕ) : d.sourceSpace n ⟶ X :=
  homMk (d.sourceSubfunctor n).ι

/-- The actual morphism between the two dimension strata. -/
def restrictedMap (n : ℕ) : d.sourceSpace n ⟶ d.targetSpace n :=
  homMk ((PointOpenSubspace.subfunctor Y.presheaf (d.targetSubset n)).fromPreimage (hom f))

theorem restriction_isPullback (n : ℕ) :
    IsPullback (hom (d.restrictedMap n)) (hom (d.sourceInclusion n))
      (hom (d.targetInclusion n)) (hom f) :=
  AffineOpenSubfunctors.isPullback_fromPreimage _ _

theorem range_sourceInclusion (n : ℕ) :
    Set.range (Points.map (hom (d.sourceInclusion n))) =
      Points.map (hom f) ⁻¹' d.targetSubset n := by
  change Set.range (Points.map (d.sourceSubfunctor n).ι) = _
  rw [sourceSubfunctor, PointOpenSubspace.preimage]
  exact PointOpenSubspace.range_points _ _

theorem source_cover (x : Points X.presheaf) :
    ∃ n : d.Index, x ∈ Set.range (Points.map (hom (d.sourceInclusion n.val))) := by
  refine ⟨⟨d.dimension (Points.map (hom f) x), ⟨_, rfl⟩⟩, ?_⟩
  rw [d.range_sourceInclusion]
  rfl

/-- A chart of a restricted map gives a chart of the original map on the same
 actual schemes. -/
def originalChart (n : ℕ) (c : EtaleMorphismChart (d.restrictedMap n)) :
    EtaleMorphismChart f where
  source := c.source
  target := c.target
  sourceMap := c.sourceMap ≫ hom (d.sourceInclusion n)
  targetMap := c.targetMap ≫ hom (d.targetInclusion n)
  schemeMap := c.schemeMap
  sourceEtale := c.sourceEtale.comp
    (PointOpenSubspace.isEtale_of_isOpenImmersion (d.sourceSubfunctor_isOpenImmersion n))
  targetEtale := c.targetEtale.comp
    (PointOpenSubspace.isEtale_of_isOpenImmersion (d.targetInclusion_isOpenImmersion n))
  comm := by
    rw [Category.assoc, ← (d.restriction_isPullback n).w,
      ← Category.assoc, c.comm, Category.assoc]

/-- The selected numerical dimension is the actual local fibre dimension of
 every chart of the restricted morphism. -/
theorem restrictedChart_localDimension (n : ℕ)
    (c : EtaleMorphismChart (d.restrictedMap n)) (x : c.source.left) :
    relativeTopologicalKrullDimAt c.schemeMap.left x = (n : WithBot ℕ∞) := by
  have hx : Points.map (hom (d.sourceInclusion n)) (chartPointMap c.sourceMap x) ∈
      Points.map (hom f) ⁻¹' d.targetSubset n := by
    rw [← d.range_sourceInclusion]
    exact ⟨_, rfl⟩
  have hdim := d.chart_spec (d.originalChart n c) x
  change d.dimension (Points.map (hom f)
    (Points.map (hom (d.sourceInclusion n)) (chartPointMap c.sourceMap x))) = n at hx
  have he : d.dimension (Points.map (hom f)
      (chartPointMap (d.originalChart n c).sourceMap x)) = n := by
    simpa only [originalChart, chartPointMap, Function.comp_apply, Points.map_comp]
      using hx
  exact hdim.symm.trans (congrArg (fun m : ℕ => (m : WithBot ℕ∞)) he)

/-- Every locally Noetherian source chart of the restriction is smooth of the
 selected fixed relative dimension. -/
theorem restrictedChart_smoothOfRelativeDimension (hf : IsSmoothMorphism f) (n : ℕ)
    (c : EtaleMorphismChart (d.restrictedMap n)) [IsLocallyNoetherian c.source.left] :
    SmoothOfRelativeDimension n c.schemeMap.left := by
  let c' := d.originalChart n c
  have hc : Smooth c.schemeMap.left :=
    hf.smooth_chart c'.sourceMap c'.targetMap c'.schemeMap
      c'.sourceEtale c'.targetEtale c'.comm
  exact smoothOfRelativeDimension_of_localDimension c.schemeMap.left hc n
    (d.restrictedChart_localDimension n c)

end SmoothTargetPointDimensions

end AlgebraicSpace

end Langlands.AlgebraicGeometry
