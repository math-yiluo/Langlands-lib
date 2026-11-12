import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionFinitePresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedFibreTargetAtlas
import Langlands.Global.AdelicSpaceSmoothModelProperties

/-! # Fixed-dimension geometry of the actual restricted models -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

namespace SmoothTargetPointDimensions

variable (d : SmoothTargetPointDimensions f)

/-- Restricting the target leaves each actual geometric fibre unchanged. -/
def restrictionFibreIso (n : ℕ) {T : Over S}
    (y : (schemeYoneda S).obj T ⟶ (d.targetSpace n).presheaf) :
    Limits.pullback (hom (d.restrictedMap n)) y ≅
      Limits.pullback (hom f) (y ≫ hom (d.targetInclusion n)) :=
  iteratedFibrePullbackIso (d.restriction_isPullback n).flip y

theorem restrictedMap_connected (hfc : HasGeometricallyConnectedFibres f) (n : ℕ) :
    HasGeometricallyConnectedFibres (d.restrictedMap n) := by
  intro K _ s y
  let := pointTopology (Limits.pullback (hom (d.restrictedMap n)) y)
  let := pointTopology (Limits.pullback (hom f) (y ≫ hom (d.targetInclusion n)))
  exact (Points.isoHomeomorph (d.restrictionFibreIso n y)).connectedSpace_iff.mpr
    (hfc K s (y ≫ hom (d.targetInclusion n)))

theorem restrictedMap_surjective (hfc : HasGeometricallyConnectedFibres f) (n : ℕ) :
    IsSurjectiveMorphism (d.restrictedMap n) :=
  (d.restrictedMap_connected hfc n).isSurjectiveMorphism

theorem restrictedMap_separated (hX : IsSeparated X) (n : ℕ) :
    IsSeparatedMorphism (d.restrictedMap n) :=
  isSeparatedMorphism_of_isSeparated_source (d.sourceSpace_isSeparated hX n) _

theorem restrictedMap_quasiCompact [IsAffine S]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hYqs : IsQuasiSeparated Y) (n : ℕ) :
    IsQuasiCompactMorphism (d.restrictedMap n) :=
  isQuasiCompactMorphism_of_atlas
    ((d.sourceSpace_finitePresentation hX n).mono (fun _ _ _ h => h.2))
    (d.targetSpace_isQuasiSeparated hYqs n) _

/-- The exact fixed-relative-dimension chart witness required by uniform
Lang-Weil, with both actual schemes affine and locally finitely presented
and both charts surjective. -/
theorem restrictedMap_fixedDimensionChart [IsAffine S] [IsLocallyNoetherian S]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (hf : IsSmoothMorphism f) (n : ℕ) :
    ∃ (U V : Over S)
      (a : (schemeYoneda S).obj U ⟶ (d.sourceSpace n).presheaf)
      (b : (schemeYoneda S).obj V ⟶ (d.targetSpace n).presheaf) (φ : U ⟶ V),
      IsAffine U.left ∧ IsAffine V.left ∧ IsEtale a ∧ IsSurjective a ∧
      IsEtale b ∧ IsSurjective b ∧ LocallyOfFinitePresentation U.hom ∧
      LocallyOfFinitePresentation V.hom ∧ SmoothOfRelativeDimension n φ.left ∧
      a ≫ hom (d.restrictedMap n) = (schemeYoneda S).map φ ≫ b := by
  obtain ⟨U, V, a, b, φ, hUa, hVa, ha, hs, hb, hbs, hUl, hVl, hw⟩ :=
    exists_affine_finitePresentation_chart_square
      (d.sourceSpace_finitePresentation hX n) (d.targetSpace_finitePresentation hY n)
      (d.targetSpace_isQuasiSeparated hYqs n) (d.restrictedMap n)
  let := hUl
  let : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  let c : EtaleMorphismChart (d.restrictedMap n) := ⟨U, V, a, b, φ, ha, hb, hw⟩
  exact ⟨U, V, a, b, φ, hUa, hVa, ha, hs, hb, hbs, hUl, hVl,
    d.restrictedChart_smoothOfRelativeDimension hf n c, hw⟩

theorem restrictedMap_smooth [IsAffine S] [IsLocallyNoetherian S]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (hf : IsSmoothMorphism f) (n : ℕ) :
    IsSmoothMorphism (d.restrictedMap n) := by
  obtain ⟨U, V, a, b, φ, _, _, ha, hs, hb, _, _, _, hφ, hw⟩ :=
    d.restrictedMap_fixedDimensionChart hX hY hYqs hf n
  let := hφ
  exact ⟨U, V, a, b, φ, ha, hs, hb, SmoothOfRelativeDimension.smooth n φ.left, hw⟩

/-- The actual restricted model satisfies the auxiliary arrow geometry. -/
def restrictedMap_auxiliaryGeometry [IsAffine S]
    (hXs : IsSeparated X)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hYqs : IsQuasiSeparated Y) (hfc : HasGeometricallyConnectedFibres f) (n : ℕ) :
    AuxiliaryMorphismGeometry (d.restrictedMap n) :=
  ⟨d.restrictedMap_separated hXs n, d.restrictedMap_quasiCompact hX hYqs n,
    d.restrictedMap_surjective hfc n⟩

end SmoothTargetPointDimensions

end Langlands.AlgebraicGeometry.AlgebraicSpace
