import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothMorphismCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.UniversallyClosedTargetAtlas
import Langlands.AlgebraicGeometry.SmoothTargetComponentRestrictions
import Langlands.AlgebraicGeometry.SmoothPureDimensionProof
import Langlands.AlgebraicGeometry.SchemeEtalePureFibreDimension

/-! # Finite locally constant relative dimensions on actual space points -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open TopologicalSpace Topology
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

namespace EtaleMorphismChart

/-- Actual local fibre dimension agrees on the represented overlap of charts. -/
theorem relativeDimension_eq_on_overlap (c d : EtaleMorphismChart f)
    (r : (sourceOverlap c d).left) :
    relativeTopologicalKrullDimAt c.schemeMap.left ((sourceFst c d).left r) =
      relativeTopologicalKrullDimAt d.schemeMap.left ((sourceSnd c d).left r) := by
  let : Etale (sourceFst c d).left :=
    d.sourceEtale.projection c.sourceMap _ _ (source_isPullback c d).flip
  let : Etale (sourceSnd c d).left :=
    c.sourceEtale.projection d.sourceMap _ _ (source_isPullback c d)
  let : Etale (targetFst c d).left :=
    d.targetEtale.projection c.targetMap _ _ (target_isPullback c d).flip
  let : Etale (targetSnd c d).left :=
    c.targetEtale.projection d.targetMap _ _ (target_isPullback c d)
  let : LocallyQuasiFinite (targetFst c d).left :=
    locallyQuasiFinite_of_etale _
  let : LocallyQuasiFinite (targetSnd c d).left :=
    locallyQuasiFinite_of_etale _
  calc
    _ = relativeTopologicalKrullDimAt
        ((sourceFst c d).left ≫ c.schemeMap.left) r :=
      (relativeTopologicalKrullDimAt_etale_source _ _ r).symm
    _ = relativeTopologicalKrullDimAt
        ((comparison c d).left ≫ (targetFst c d).left) r := by
      change relativeTopologicalKrullDimAt (sourceFst c d ≫ c.schemeMap).left r =
        relativeTopologicalKrullDimAt (comparison c d ≫ targetFst c d).left r
      rw [comparison_fst]
    _ = relativeTopologicalKrullDimAt (comparison c d).left r :=
      relativeTopologicalKrullDimAt_locallyQuasiFinite_target _ _ r
    _ = relativeTopologicalKrullDimAt
        ((comparison c d).left ≫ (targetSnd c d).left) r :=
      (relativeTopologicalKrullDimAt_locallyQuasiFinite_target _ _ r).symm
    _ = relativeTopologicalKrullDimAt
        ((sourceSnd c d).left ≫ d.schemeMap.left) r := by
      change relativeTopologicalKrullDimAt (comparison c d ≫ targetSnd c d).left r =
        relativeTopologicalKrullDimAt (sourceSnd c d ≫ d.schemeMap).left r
      rw [comparison_snd]
    _ = _ := relativeTopologicalKrullDimAt_etale_source _ _ r

/-- Relative local dimension depends only on the actual quotient source point. -/
theorem relativeDimension_eq_of_point_eq (c d : EtaleMorphismChart f)
    (x : c.source.left) (y : d.source.left)
    (h : chartPointMap c.sourceMap x = chartPointMap d.sourceMap y) :
    relativeTopologicalKrullDimAt c.schemeMap.left x =
      relativeTopologicalKrullDimAt d.schemeMap.left y := by
  obtain ⟨r, hry, hrx⟩ := (chartPointMap_eq_iff_exists_pullback
    d.sourceMap c.sourceMap c.sourceEtale.representable y x).mp h.symm
  simpa only [sourceFst, sourceSnd, hrx, hry] using
    relativeDimension_eq_on_overlap c d r

section Smooth

variable (c : EtaleMorphismChart f) [IsLocallyNoetherian c.source.left]
    (hc : Smooth c.schemeMap.left)

/-- Select the actual smooth chart dimension on each source component. -/
def sourceComponentDimensions : _root_.ConnectedComponents c.source.left → ℕ :=
  fun i => Classical.choose (smoothConnectedRelativeDimension
    (componentScheme c.source.left i) c.target.left
    (componentι c.source.left i ≫ c.schemeMap.left)
    (by let := hc; infer_instance) inferInstance)

theorem sourceComponentDimensions_spec (i : _root_.ConnectedComponents c.source.left) :
    SmoothOfRelativeDimension (sourceComponentDimensions c hc i)
      (componentι c.source.left i ≫ c.schemeMap.left) :=
  Classical.choose_spec (smoothConnectedRelativeDimension
    (componentScheme c.source.left i) c.target.left
    (componentι c.source.left i ≫ c.schemeMap.left)
    (by let := hc; infer_instance) inferInstance)

/-- The natural-number dimension at an ordinary point of the source chart. -/
def sourcePointDimension (x : c.source.left) : ℕ :=
  sourceComponentDimensions c hc (_root_.ConnectedComponents.mk x)

theorem sourcePointDimension_spec (x : c.source.left) :
    relativeTopologicalKrullDimAt c.schemeMap.left x =
      (sourcePointDimension c hc x : WithBot ℕ∞) := by
  let i := _root_.ConnectedComponents.mk x
  let z : componentScheme c.source.left i := ⟨x, rfl⟩
  have hd := smoothPureDimension.2 _ _
    (componentι c.source.left i ≫ c.schemeMap.left)
    (sourceComponentDimensions c hc i) (sourceComponentDimensions_spec c hc i)
  have hlocal := (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq
    (componentι c.source.left i ≫ c.schemeMap.left)
    (sourceComponentDimensions c hc i)).mp hd z
  exact (relativeTopologicalKrullDimAt_etale_source
    (componentι c.source.left i) c.schemeMap.left z).symm.trans hlocal

theorem sourcePointDimension_isLocallyConstant :
    IsLocallyConstant (sourcePointDimension c hc) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨componentOpen c.source.left (_root_.ConnectedComponents.mk x),
    (componentOpen _ _).isOpen, rfl, ?_⟩
  intro y hy
  exact congrArg (sourceComponentDimensions c hc) hy

variable (hs : IsSurjective c.sourceMap)

/-- A dimension function on the actual quotient point set, chosen through an atlas. -/
def pointDimension (x : Points X.presheaf) : ℕ :=
  sourcePointDimension c hc (Classical.choose (surjective_chartPointMap c.sourceMap hs x))

/-- Every other commuting etale chart computes the same actual local dimension. -/
theorem pointDimension_spec (d : EtaleMorphismChart f) (x : d.source.left) :
    (pointDimension c hc hs (chartPointMap d.sourceMap x) : WithBot ℕ∞) =
      relativeTopologicalKrullDimAt d.schemeMap.left x := by
  let z := Classical.choose (surjective_chartPointMap c.sourceMap hs
    (chartPointMap d.sourceMap x))
  have hz : chartPointMap c.sourceMap z = chartPointMap d.sourceMap x :=
    Classical.choose_spec (surjective_chartPointMap c.sourceMap hs _)
  exact (sourcePointDimension_spec c hc z).symm.trans
    (relativeDimension_eq_of_point_eq c d z x hz)

theorem pointDimension_chart (x : c.source.left) :
    pointDimension c hc hs (chartPointMap c.sourceMap x) = sourcePointDimension c hc x := by
  have h := (pointDimension_spec c hc hs c x).trans (sourcePointDimension_spec c hc x)
  exact_mod_cast h

theorem pointDimension_isLocallyConstant :
    @IsLocallyConstant (Points X.presheaf) ℕ (pointTopology X.presheaf)
      (pointDimension c hc hs) := by
  intro A
  apply (isOpen_pointTopology_iff_atlas c.sourceMap c.sourceEtale hs _).mpr
  have he : chartPointMap c.sourceMap ⁻¹' (pointDimension c hc hs ⁻¹' A) =
      sourcePointDimension c hc ⁻¹' A := by
    ext x
    simp only [Set.mem_preimage, pointDimension_chart]
  rw [he]
  exact sourcePointDimension_isLocallyConstant c hc A

theorem pointDimension_range_finite [CompactSpace c.source.left] :
    (Set.range (pointDimension c hc hs)).Finite := by
  apply (sourcePointDimension_isLocallyConstant c hc).range_finite.subset
  rintro n ⟨x, rfl⟩
  exact ⟨_, rfl⟩

end Smooth

end EtaleMorphismChart

/-- The smooth chart square proves openness on the ordinary point topologies. -/
theorem IsSmoothMorphism.isOpenMap_points (hf : IsSmoothMorphism f) :
    @IsOpenMap (Points X.presheaf) (Points Y.presheaf)
      (pointTopology X.presheaf) (pointTopology Y.presheaf) (Points.map (hom f)) := by
  let := pointTopology X.presheaf
  let := pointTopology Y.presheaf
  obtain ⟨U, V, a, b, φ, ha, hs, hb, hφ, hw⟩ := hf
  let := hφ
  intro O hO
  have he : Points.map (hom f) '' O =
      chartPointMap b '' (φ.left '' (chartPointMap a ⁻¹' O)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨u, rfl⟩ := surjective_chartPointMap a hs x
      refine ⟨φ.left u, ⟨u, hx, rfl⟩, ?_⟩
      change _ = Points.map (hom f) (Points.map a (schemePoint U u))
      rw [← Points.map_comp, hw]
      exact (chartPointMap_comp φ b u).symm
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨chartPointMap a u, hu, ?_⟩
      change Points.map (hom f) (Points.map a (schemePoint U u)) = _
      rw [← Points.map_comp, hw]
      exact chartPointMap_comp φ b u
  rw [he]
  exact isOpen_image_chartPointMap b hb
    (φ.left.isOpenMap _ (hO.preimage (continuous_schemePoint_chart a ha)))

/-- A locally constant function on the source is constant on every fibre when
the actual geometric-fibre point spaces are connected and nonempty. -/
theorem HasGeometricallyConnectedFibres.locallyConstant_eq_of_map_eq
    (hf : HasGeometricallyConnectedFibres f)
    {D : Points X.presheaf → ℕ}
    (hD : @IsLocallyConstant (Points X.presheaf) ℕ (pointTopology X.presheaf) D)
    (x z : Points X.presheaf) (h : Points.map (hom f) x = Points.map (hom f) z) :
    D x = D z := by
  let := pointTopology X.presheaf
  obtain ⟨p, hp⟩ := Quot.exists_rep (Points.map (hom f) x)
  let T : Over S := Over.mk p.base
  let y : (schemeYoneda S).obj T ⟶ Y.presheaf := uliftYonedaEquiv.{u + 1}.symm p.val
  let q : Points ((schemeYoneda S).obj T) := schemePoint T (IsLocalRing.closedPoint p.field)
  have hq : Points.map y q = Points.map (hom f) x :=
    (chartPointMap_fieldPoint p).trans hp
  obtain ⟨a, hax, _⟩ := Points.exists_pullback_point (hom f) y x q hq.symm
  obtain ⟨b, hbz, _⟩ := Points.exists_pullback_point (hom f) y z q (h.symm.trans hq.symm)
  let := pointTopology (Limits.pullback (hom f) y)
  let := hf p.field p.base y
  obtain ⟨V, v, hv, hvs⟩ := X.property.2
  have hcont := Points.continuous_map_of_atlas (pullback.fst (hom f) y) v hv hvs
  have hc := hD.comp_continuous hcont
  have he := hc.apply_eq_of_preconnectedSpace a b
  simpa only [Function.comp_apply, hax, hbz] using he

/-- A finite locally constant dimension on the target, compatible with every
actual commuting etale chart square. -/
structure SmoothTargetPointDimensions (f : X ⟶ Y) where
  dimension : Points Y.presheaf → ℕ
  locallyConstant :
    @IsLocallyConstant (Points Y.presheaf) ℕ (pointTopology Y.presheaf) dimension
  finite_range : (Set.range dimension).Finite
  chart_spec : ∀ (c : EtaleMorphismChart f) (x : c.source.left),
    (dimension (Points.map (hom f) (chartPointMap c.sourceMap x)) : WithBot ℕ∞) =
      relativeTopologicalKrullDimAt c.schemeMap.left x

/-- Separated finite-presentation models of a smooth surjection with connected
geometric fibres have finitely many locally constant target dimensions. -/
def smoothTargetPointDimensions [IsAffine S] [IsLocallyNoetherian S]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (hf : IsSmoothMorphism f)
    (hfs : IsSurjectiveMorphism f) (hfc : HasGeometricallyConnectedFibres f) :
    SmoothTargetPointDimensions f := by
  apply Classical.choice
  let := pointTopology X.presheaf
  let := pointTopology Y.presheaf
  obtain ⟨U, V, a, b, φ, hUa, hVa, ha, hs, hb, hbs, hUl, hVl, hw⟩ :=
    exists_affine_finitePresentation_chart_square hX hY hYqs f
  let := hUa
  let := hUl
  let : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  let c : EtaleMorphismChart f := ⟨U, V, a, b, φ, ha, hb, hw⟩
  have hc : Smooth c.schemeMap.left := hf.smooth_chart a b φ ha hb hw
  let D := c.pointDimension hc hs
  have hD := c.pointDimension_isLocallyConstant hc hs
  let E : Points Y.presheaf → ℕ :=
    fun y => D (Classical.choose (hfs y))
  have he (x : Points X.presheaf) : E (Points.map (hom f) x) = D x :=
    hfc.locallyConstant_eq_of_map_eq hD _ x (Classical.choose_spec (hfs _))
  refine ⟨⟨E, ?_, ?_, ?_⟩⟩
  · intro A
    have heq : E ⁻¹' A = Points.map (hom f) '' (D ⁻¹' A) := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := hfs y
        exact ⟨x, by simpa only [Set.mem_preimage, he] using hy, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        simpa only [Set.mem_preimage, he] using hx
    rw [heq]
    exact hf.isOpenMap_points _ (hD A)
  · apply (c.pointDimension_range_finite hc hs).subset
    rintro n ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · intro d x
    rw [he]
    exact c.pointDimension_spec hc hs d x

end Langlands.AlgebraicGeometry.AlgebraicSpace
