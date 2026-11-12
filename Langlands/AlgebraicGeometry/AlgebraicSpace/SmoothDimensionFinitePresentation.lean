import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionRestrictions
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationChartSquares

/-! # Finite-presentation atlases on clopen dimension restrictions -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open TopologicalSpace Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace PointOpenSubspace

variable (Y : AlgebraicSpace S) (O : Set (Points Y.presheaf))
  (hO : IsOpen[pointTopology Y.presheaf] O)

/-- The restricted chart maps to the actual point-selected open subspace. -/
def chartToSpace {T : Over S} (a : (schemeYoneda S).obj T ⟶ Y.presheaf) :
    (schemeYoneda S).obj (chartScheme Y O hO a) ⟶ (space Y O hO).presheaf :=
  Subfunctor.lift ((schemeYoneda S).map (chartInclusion Y O hO a) ≫ a) (by
    rw [Subfunctor.range_comp, Subfunctor.image_le_iff, range_chartInclusion])

theorem chartToSpace_comp {T : Over S}
    (a : (schemeYoneda S).obj T ⟶ Y.presheaf) :
    chartToSpace Y O hO a ≫ hom (inclusion Y O hO) =
      (schemeYoneda S).map (chartInclusion Y O hO a) ≫ a :=
  Subfunctor.lift_ι _ _

/-- The explicit scheme restriction is the actual atlas pullback. -/
theorem chartToSpace_isPullback {T : Over S}
    (a : (schemeYoneda S).obj T ⟶ Y.presheaf) :
    IsPullback (chartToSpace Y O hO a)
      ((schemeYoneda S).map (chartInclusion Y O hO a))
      (hom (inclusion Y O hO)) a := by
  let j := chartInclusion Y O hO a
  let : _root_.AlgebraicGeometry.IsOpenImmersion j.left :=
    chartInclusion_isOpenImmersion Y O hO a
  let : Mono j := Over.mono_of_mono_left j
  exact OpenSubfunctorLifting.isPullback_subfunctor_of_range
    (subfunctor Y.presheaf O) _ _ _ (chartToSpace_comp Y O hO a)
    (range_chartInclusion Y O hO a)

theorem chartToSpace_isEtale {T : Over S}
    (a : (schemeYoneda S).obj T ⟶ Y.presheaf) (ha : IsEtale a) :
    IsEtale (chartToSpace Y O hO a) := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S)) (chartToSpace_isPullback Y O hO a).flip ha

theorem chartToSpace_isSurjective {T : Over S}
    (a : (schemeYoneda S).obj T ⟶ Y.presheaf) (ha : IsSurjective a) :
    IsSurjective (chartToSpace Y O hO a) := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) (chartToSpace_isPullback Y O hO a).flip ha

/-- A clopen restriction of a compact scheme chart remains compact. -/
theorem chartScheme_compactSpace
    (hOc : IsClosed[pointTopology Y.presheaf] O) {T : Over S}
    [CompactSpace T.left] (a : (schemeYoneda S).obj T ⟶ Y.presheaf) :
    CompactSpace (chartScheme Y O hO a).left := by
  let := pointTopology Y.presheaf
  exact isCompact_iff_compactSpace.mp ((hOc.preimage (continuous_chart Y a)).isCompact)

/-- Clopen point restrictions retain an actual finite-presentation compact atlas. -/
theorem hasAtlasProperty_finitePresentation [IsAffine S]
    (hOc : IsClosed[pointTopology Y.presheaf] O)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u})
      (space Y O hO) := by
  obtain ⟨T, a, ha, hs, hl, hq⟩ := hY
  let : LocallyOfFinitePresentation T.hom := hl
  let : QuasiCompact T.hom := hq
  let : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  let : CompactSpace (chartScheme Y O hO a).left :=
    chartScheme_compactSpace Y O hO hOc a
  let : _root_.AlgebraicGeometry.IsOpenImmersion (chartOpen Y O hO a).ι := inferInstance
  refine ⟨chartScheme Y O hO a, chartToSpace Y O hO a,
    chartToSpace_isEtale Y O hO a ha, chartToSpace_isSurjective Y O hO a hs, ?_, ?_⟩
  · exact inferInstanceAs
      (LocallyOfFinitePresentation ((chartOpen Y O hO a).ι ≫ T.hom))
  · infer_instance

/-- A point-selected open subspace inherits separatedness. -/
theorem isSeparated (hY : IsSeparated Y) : IsSeparated (space Y O hO) :=
  OpenSubfunctorImages.isClosedImmersion_diag_subfunctor hY _

end PointOpenSubspace

namespace SmoothTargetPointDimensions

variable {X Y : AlgebraicSpace S} {f : X ⟶ Y} (d : SmoothTargetPointDimensions f)

/-- Every target dimension stratum retains a finite-presentation atlas. -/
theorem targetSpace_finitePresentation [IsAffine S]
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (n : ℕ) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u})
      (d.targetSpace n) :=
  PointOpenSubspace.hasAtlasProperty_finitePresentation Y _ _
    (d.targetSubset_isClosed n) hY

theorem targetSpace_isSeparated (hY : IsSeparated Y) (n : ℕ) :
    IsSeparated (d.targetSpace n) :=
  PointOpenSubspace.isSeparated Y _ _ hY

theorem targetSpace_isQuasiSeparated (hY : IsQuasiSeparated Y) (n : ℕ) :
    IsQuasiSeparated (d.targetSpace n) :=
  OpenSubspaceGeometry.isQuasiSeparated_openSubspace hY _
    (d.targetInclusion_isOpenImmersion n)

/-- Every source dimension restriction retains a finite-presentation atlas. -/
theorem sourceSpace_finitePresentation [IsAffine S]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (n : ℕ) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u})
      (d.sourceSpace n) := by
  let := pointTopology X.presheaf
  let := pointTopology Y.presheaf
  have hc : Continuous (Points.map (hom f)) := by
    obtain ⟨V, a, ha, hs⟩ := Y.property.2
    exact Points.continuous_map_of_atlas (hom f) a ha hs
  have ho := (d.targetSubset_isOpen n).preimage hc
  have hclosed := (d.targetSubset_isClosed n).preimage hc
  have h := PointOpenSubspace.hasAtlasProperty_finitePresentation X
    (Points.map (hom f) ⁻¹' d.targetSubset n) ho hclosed hX
  simpa only [PointOpenSubspace.space, sourceSpace, sourceSubfunctor,
    PointOpenSubspace.preimage] using h

theorem sourceSpace_isSeparated (hX : IsSeparated X) (n : ℕ) :
    IsSeparated (d.sourceSpace n) :=
  OpenSubfunctorImages.isClosedImmersion_diag_subfunctor hX _

theorem sourceSpace_isQuasiSeparated (hX : IsQuasiSeparated X) (n : ℕ) :
    IsQuasiSeparated (d.sourceSpace n) :=
  OpenSubspaceGeometry.isQuasiSeparated_openSubspace hX _
    (d.sourceSubfunctor_isOpenImmersion n)

end SmoothTargetPointDimensions

end Langlands.AlgebraicGeometry.AlgebraicSpace
