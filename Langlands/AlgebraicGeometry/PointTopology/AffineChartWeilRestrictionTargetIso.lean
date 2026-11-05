import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionLocalTopology

/-! # Target morphisms and isomorphisms for actual affine-chart Weil restriction -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable {Y Z W : Over (Spec (CommRingCat.of B))}
  [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType W.hom]

/-- A target morphism induces the original counit-defined morphism of actual Weil schemes. -/
def affineChartWeilRestrictionTargetMap [IsSeparated Z.hom]
    (hZ : HasFiniteAffineNeighborhoods Z.left) (f : Y ⟶ Z) :
    affineChartWeilRestriction A B Y ⟶ affineChartWeilRestriction A B Z :=
  (affineChartWeilRestrictionTestEquiv A B Z hZ (affineChartWeilRestriction A B Y)).symm
    (affineChartWeilRestrictionCounit A B Y ≫ f)

/-- The induced target map recovers the original counit followed by the given target morphism. -/
@[simp]
theorem affineChartWeilRestrictionTargetMap_counit [IsSeparated Z.hom]
    (hZ : HasFiniteAffineNeighborhoods Z.left) (f : Y ⟶ Z) :
    affineChartWeilRestrictionComparison A B Z (affineChartWeilRestriction A B Y)
        (affineChartWeilRestrictionTargetMap A B hZ f) =
      affineChartWeilRestrictionCounit A B Y ≫ f :=
  (affineChartWeilRestrictionTestEquiv A B Z hZ _).apply_symm_apply _

/-- On every actual test, the induced map is postcomposition of the original Weil comparison. -/
@[simp]
theorem affineChartWeilRestrictionTargetMap_comparison [IsSeparated Z.hom]
    (hZ : HasFiniteAffineNeighborhoods Z.left) (f : Y ⟶ Z)
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionComparison A B Z T
        (p ≫ affineChartWeilRestrictionTargetMap A B hZ f) =
      affineChartWeilRestrictionComparison A B Y T p ≫ f := by
  rw [affineChartWeilRestrictionComparison_natural,
    affineChartWeilRestrictionTargetMap_counit]
  exact (Category.assoc _ _ _).symm

@[simp]
theorem affineChartWeilRestrictionTargetMap_id [IsSeparated Y.hom]
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    affineChartWeilRestrictionTargetMap A B hY (𝟙 Y) = 𝟙 _ := by
  apply affineChartWeilRestrictionComparison_injective A B Y
  rw [affineChartWeilRestrictionTargetMap_counit]
  simp [affineChartWeilRestrictionComparison]
  exact (Category.id_comp _).symm

/-- Target maps preserve composition as actual scheme morphisms. -/
theorem affineChartWeilRestrictionTargetMap_comp [IsSeparated Z.hom] [IsSeparated W.hom]
    (hZ : HasFiniteAffineNeighborhoods Z.left) (hW : HasFiniteAffineNeighborhoods W.left)
    (f : Y ⟶ Z) (g : Z ⟶ W) :
    affineChartWeilRestrictionTargetMap A B hW (f ≫ g) =
      affineChartWeilRestrictionTargetMap A B hZ f ≫
        affineChartWeilRestrictionTargetMap A B hW g := by
  apply affineChartWeilRestrictionComparison_injective A B W
  rw [affineChartWeilRestrictionTargetMap_counit,
    affineChartWeilRestrictionTargetMap_comparison,
    affineChartWeilRestrictionTargetMap_counit]
  exact (Category.assoc _ _ _).symm

/-- An original target isomorphism induces a counit-compatible isomorphism of actual Weil schemes. -/
def affineChartWeilRestrictionTargetIso [IsSeparated Y.hom] [IsSeparated Z.hom]
    (hY : HasFiniteAffineNeighborhoods Y.left) (hZ : HasFiniteAffineNeighborhoods Z.left)
    (e : Y ≅ Z) : affineChartWeilRestriction A B Y ≅ affineChartWeilRestriction A B Z where
  hom := affineChartWeilRestrictionTargetMap A B hZ e.hom
  inv := affineChartWeilRestrictionTargetMap A B hY e.inv
  hom_inv_id := by
    rw [← affineChartWeilRestrictionTargetMap_comp, e.hom_inv_id,
      affineChartWeilRestrictionTargetMap_id]
  inv_hom_id := by
    rw [← affineChartWeilRestrictionTargetMap_comp, e.inv_hom_id,
      affineChartWeilRestrictionTargetMap_id]

/-- The actual target isomorphism preserves the original comparison on every test. -/
@[simp]
theorem affineChartWeilRestrictionTargetIso_comparison [IsSeparated Y.hom] [IsSeparated Z.hom]
    (hY : HasFiniteAffineNeighborhoods Y.left) (hZ : HasFiniteAffineNeighborhoods Z.left)
    (e : Y ≅ Z) (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionComparison A B Z T
        (p ≫ (affineChartWeilRestrictionTargetIso A B hY hZ e).hom) =
      affineChartWeilRestrictionComparison A B Y T p ≫ e.hom :=
  affineChartWeilRestrictionTargetMap_comparison A B hZ e.hom T p

end Langlands.AlgebraicGeometry.PointTopology
