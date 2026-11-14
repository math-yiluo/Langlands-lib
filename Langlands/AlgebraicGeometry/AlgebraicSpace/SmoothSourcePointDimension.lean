import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionRestrictions
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedStructuralFibres

/-! # Intrinsic dimensions of arbitrary smooth spaces over a field -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionPieces

variable {K : Type u} [Field K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Any etale scheme chart gives a chart square for the structure map. -/
abbrev structuralChart {U : Over (Spec (CommRingCat.of K))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) :
    EtaleMorphismChart (structuralMorphism X) where
  source := U
  target := Over.mk (𝟙 _)
  sourceMap := a
  targetMap := 𝟙 _
  schemeMap := Over.homMk U.hom (by simp)
  sourceEtale := ha
  targetEtale := by
    simpa using isEtale_map (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of K)))))
      (by change Etale (𝟙 _); infer_instance)
  comm := (basePresheafIsTerminal _).hom_ext _ _

variable (hX : SmoothOverBase X)

/-- A chosen actual smooth surjective etale scheme atlas, without compactness. -/
def atlas : Over (Spec (CommRingCat.of K)) := Classical.choose hX

def atlasMap : (schemeYoneda _).obj (atlas hX) ⟶ X.presheaf :=
  Classical.choose (Classical.choose_spec hX)

theorem atlasMap_isEtale : IsEtale (atlasMap hX) :=
  (Classical.choose_spec (Classical.choose_spec hX)).1

theorem atlasMap_isSurjective : IsSurjective (atlasMap hX) :=
  (Classical.choose_spec (Classical.choose_spec hX)).2.1

theorem atlas_smooth : Smooth (atlas hX).hom :=
  (Classical.choose_spec (Classical.choose_spec hX)).2.2

instance atlas_isLocallyNoetherian : IsLocallyNoetherian (atlas hX).left := by
  let := atlas_smooth hX
  exact LocallyOfFiniteType.isLocallyNoetherian (atlas hX).hom

/-- The witnessing chart square for structural smoothness. -/
abbrev atlasChart : EtaleMorphismChart (structuralMorphism X) :=
  structuralChart (atlasMap hX) (atlasMap_isEtale hX)

/-- Intrinsic natural-number dimension on the actual ordinary point quotient. -/
def pointDimension : Points X.presheaf → ℕ :=
  (atlasChart hX).pointDimension (atlas_smooth hX) (atlasMap_isSurjective hX)

/-- Every commuting etale chart computes this same local relative dimension. -/
theorem pointDimension_spec (c : EtaleMorphismChart (structuralMorphism X))
    (x : c.source.left) :
    (pointDimension hX (chartPointMap c.sourceMap x) : WithBot ℕ∞) =
      relativeTopologicalKrullDimAt c.schemeMap.left x :=
  (atlasChart hX).pointDimension_spec (atlas_smooth hX) (atlasMap_isSurjective hX) c x

/-- In a scheme chart over the field this is the actual structural local dimension. -/
theorem pointDimension_chart {U : Over (Spec (CommRingCat.of K))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) (x : U.left) :
    (pointDimension hX (chartPointMap a x) : WithBot ℕ∞) =
      relativeTopologicalKrullDimAt U.hom x :=
  pointDimension_spec hX (structuralChart a ha) x

theorem pointDimension_isLocallyConstant :
    @IsLocallyConstant (Points X.presheaf) ℕ (pointTopology X.presheaf)
      (pointDimension hX) :=
  (atlasChart hX).pointDimension_isLocallyConstant
    (atlas_smooth hX) (atlasMap_isSurjective hX)

/-- The numerical function agrees with the construction through any smooth atlas. -/
theorem pointDimension_eq_of_atlas {U : Over (Spec (CommRingCat.of K))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) (hU : Smooth U.hom)
    [IsLocallyNoetherian U.left] :
    pointDimension hX = (structuralChart a ha).pointDimension hU hs := by
  funext p
  obtain ⟨x, rfl⟩ := surjective_chartPointMap a hs p
  have h := (pointDimension_chart hX a ha x).trans
    ((structuralChart a ha).pointDimension_spec hU hs (structuralChart a ha) x).symm
  exact_mod_cast h

/-- In particular, changing the witnessing smoothness proof changes no value. -/
theorem pointDimension_independent (hX' : SmoothOverBase X) :
    pointDimension hX = pointDimension hX' :=
  pointDimension_eq_of_atlas hX (atlasMap hX') (atlasMap_isEtale hX')
    (atlasMap_isSurjective hX') (atlas_smooth hX')

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionPieces
