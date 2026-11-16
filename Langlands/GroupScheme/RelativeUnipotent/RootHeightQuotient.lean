import Langlands.GroupScheme.RelativeUnipotent.RootHeightLayer
import Langlands.GroupScheme.VectorCoordinateBlockQuotient

/-! # Represented quotients of root-height terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical Opposite
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeUnipotent.RootHeightChart

open LocalSplitCell Langlands.GroupTheory VectorGroup.CoordinateBlock

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} (C : RootHeightChart U)

/-- Points of a represented height term as elements of the generated subgroup. -/
def pointInLevel (T : Over (Spec (CommRingCat.of R))) (d : ℕ) :
    (T ⟶ (C.groupScheme d).X) →*
      HeightFiltration.level (rootFactor C.roots ULift.up T) C.height d where
  toFun x := ⟨x ≫ (C.inclusion d).hom.hom, by
    change _ ∈ (C.subgroup d).carrier T
    rw [← (C.isRepresentedBy_inclusion d).2]
    exact ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp _ _ _)

/-- The all-test quotient homomorphism, before applying Yoneda. -/
def quotientPoints (T : Over (Spec (CommRingCat.of R))) (d : ℕ) (hd : 0 < d) :
    (T ⟶ (C.groupScheme d).X) →*
      (T ⟶ (VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (C.exactSupport d))).X) :=
  (VectorGroup.coordinates (CommRingCat.of R) (Nat.card (C.exactSupport d)) T).symm.toMonoidHom.comp
    ((C.layerCoordinates T d hd).comp (C.pointInLevel T d))

theorem quotientPoints_coord (T : Over (Spec (CommRingCat.of R)))
    (d : ℕ) (hd : 0 < d) (x : T ⟶ (C.groupScheme d).X)
    (j : Fin (Nat.card (C.exactSupport d))) :
    (VectorGroup.coordinates (CommRingCat.of R) _ T
      (C.quotientPoints T d hd x)).toAdd j =
      C.coordinates T (x ≫ (C.inclusion d).hom.hom) (C.exactEnumeration d j).val := by
  change ((VectorGroup.coordinates (CommRingCat.of R) _ T)
    ((VectorGroup.coordinates (CommRingCat.of R) _ T).symm
      (C.layerCoordinates T d hd (C.pointInLevel T d x)))).toAdd j = _
  rw [MulEquiv.apply_symm_apply, layerCoordinates_apply]
  rfl

theorem coordinates_comp {T W : Over (Spec (CommRingCat.of R))}
    (f : W ⟶ T) (x : T ⟶ U.X) :
    C.coordinates W (f ≫ x) = fun k => f.left.appTop (C.coordinates T x k) := by
  unfold coordinates
  rw [Category.assoc, VectorGroup.coordinates_comp]

theorem quotientPoints_natural (d : ℕ) (hd : 0 < d)
    {T W : Over (Spec (CommRingCat.of R))} (f : W ⟶ T)
    (x : T ⟶ (C.groupScheme d).X) :
    C.quotientPoints W d hd (f ≫ x) = f ≫ C.quotientPoints T d hd x := by
  apply VectorGroup.points_ext
  intro j
  rw [quotientPoints_coord, VectorGroup.coordinates_comp]
  dsimp only
  rw [quotientPoints_coord, Category.assoc, coordinates_comp]

/-- The actual exact-height quotient homomorphism to a standard vector group. -/
def quotientMap (d : ℕ) (hd : 0 < d) :
    C.groupScheme d ⟶
      VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (C.exactSupport d)) :=
  homOfPoints (fun T => C.quotientPoints T d hd) (C.quotientPoints_natural d hd)

@[simp]
theorem comp_quotientMap (d : ℕ) (hd : 0 < d)
    (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (C.groupScheme d).X) :
    x ≫ (C.quotientMap d hd).hom.hom = C.quotientPoints T d hd x :=
  comp_homOfPoints _ _ T x

/-- The original coordinates of a point of a represented term are extension by
zero of its own standard affine-space coordinates. -/
theorem coordinates_inclusion (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (C.groupScheme d).X) (k : Fin C.dimension) :
    C.coordinates T (x ≫ (C.inclusion d).hom.hom) k =
      if hk : k ∈ C.support d then
        (VectorGroup.coordinates (CommRingCat.of R) _ T x).toAdd
          ((C.enumeration d).symm ⟨k, hk⟩) else 0 := by
  unfold coordinates inclusion
  rw [CoordinateFiltrationTerm.inclusion_hom]
  simp only [CoordinateFiltrationTerm.schemeInclusion, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, comp_blockInclusion, blockPoints_coord]

/-- Inside the coordinate affine space of a height term, select the exact height. -/
def selectedSupport (d : ℕ) : Set (Fin (Nat.card (C.support d))) :=
  {a | C.height (C.enumeration d a).val = d}

/-- The exact-height root enumeration, expressed in the coordinates of the term. -/
def selectedEnumeration (d : ℕ) :
    Fin (Nat.card (C.exactSupport d)) ≃ C.selectedSupport d where
  toFun j := ⟨(C.enumeration d).symm
      ⟨(C.exactEnumeration d j).val, Nat.le_of_eq (C.exactEnumeration d j).property.symm⟩,
    by
      change C.height ((C.enumeration d) ((C.enumeration d).symm _)).val = d
      rw [Equiv.apply_symm_apply]
      exact (C.exactEnumeration d j).property⟩
  invFun a := (C.exactEnumeration d).symm
    ⟨(C.enumeration d a.val).val, a.property⟩
  left_inv j := by simp
  right_inv a := by
    apply Subtype.ext
    simp

/-- The quotient's scheme morphism is exactly ordinary coordinate projection.
Its source has a transferred group law, but the same affine-space scheme. -/
theorem quotientMap_hom (d : ℕ) (hd : 0 < d) :
    (C.quotientMap d hd).hom.hom =
      (coordinateProjection (CommRingCat.of R)
        (C.selectedSupport d) (C.selectedEnumeration d)).hom.hom := by
  apply yoneda.map_injective
  ext T x
  change x ≫ (C.quotientMap d hd).hom.hom =
    x ≫ (coordinateProjection (CommRingCat.of R) _ _).hom.hom
  rw [comp_quotientMap, comp_blockRestriction]
  apply VectorGroup.points_ext
  intro j
  rw [quotientPoints_coord, blockRestrictionPoints_coord, coordinates_inclusion]
  have hj : (C.exactEnumeration d j).val ∈ C.support d :=
    Nat.le_of_eq (C.exactEnumeration d j).property.symm
  rw [dite_eq_left hj]
  rfl

theorem flat_quotientMap (d : ℕ) (hd : 0 < d) :
    Flat (C.quotientMap d hd).hom.hom.left := by
  rw [quotientMap_hom]
  exact flat_coordinateProjection _ _ _

theorem surjective_quotientMap (d : ℕ) (hd : 0 < d) :
    Surjective (C.quotientMap d hd).hom.hom.left := by
  rw [quotientMap_hom]
  exact surjective_coordinateProjection _ _ _

theorem locallyOfFinitePresentation_quotientMap (d : ℕ) (hd : 0 < d) :
    LocallyOfFinitePresentation (C.quotientMap d hd).hom.hom.left := by
  rw [quotientMap_hom]
  exact locallyOfFinitePresentation_coordinateProjection _ _ _

end Langlands.GroupScheme.RelativeUnipotent.RootHeightChart
