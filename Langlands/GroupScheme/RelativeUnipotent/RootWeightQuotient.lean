import Langlands.GroupScheme.RelativeUnipotent.RootWeightLayer
import Langlands.GroupScheme.RelativeUnipotent.RootHeightQuotient
import Langlands.GroupScheme.VectorCoordinateBlockQuotient

/-! # Represented quotients of positive-weight terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical Opposite
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Langlands.GroupTheory VectorGroup.CoordinateBlock

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} {C : RootHeightChart U}
    (W : RootWeightData C)

/-- Points of a represented positive-weight term as elements of the generated subgroup. -/
def pointInLevel (T : Over (Spec (CommRingCat.of R))) (d : ℕ) :
    (T ⟶ (W.groupScheme d).X) →*
      HeightFiltration.level (rootFactor C.roots ULift.up T) W.weight (d + 1) where
  toFun x := ⟨x ≫ (W.inclusion d).hom.hom, by
    change _ ∈ (W.subgroup d).carrier T
    rw [← (W.isRepresentedBy_inclusion d).2]
    exact ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp _ _ _)

/-- The all-test quotient homomorphism, before applying Yoneda. -/
def quotientPoints (T : Over (Spec (CommRingCat.of R))) (d : ℕ) :
    (T ⟶ (W.groupScheme d).X) →*
      (T ⟶ (VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (W.exactSupport d))).X) :=
  (VectorGroup.coordinates (CommRingCat.of R) (Nat.card (W.exactSupport d)) T).symm.toMonoidHom.comp
    ((W.layerCoordinates T d).comp (W.pointInLevel T d))

theorem quotientPoints_coord (T : Over (Spec (CommRingCat.of R)))
    (d : ℕ) (x : T ⟶ (W.groupScheme d).X)
    (j : Fin (Nat.card (W.exactSupport d))) :
    (VectorGroup.coordinates (CommRingCat.of R) _ T
      (W.quotientPoints T d x)).toAdd j =
      C.coordinates T (x ≫ (W.inclusion d).hom.hom) (W.exactEnumeration d j).val := by
  change ((VectorGroup.coordinates (CommRingCat.of R) _ T)
    ((VectorGroup.coordinates (CommRingCat.of R) _ T).symm
      (W.layerCoordinates T d (W.pointInLevel T d x)))).toAdd j = _
  rw [MulEquiv.apply_symm_apply, layerCoordinates_apply]
  rfl

theorem quotientPoints_natural (d : ℕ)
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (x : T ⟶ (W.groupScheme d).X) :
    W.quotientPoints T' d (f ≫ x) = f ≫ W.quotientPoints T d x := by
  apply VectorGroup.points_ext
  intro j
  rw [quotientPoints_coord, VectorGroup.coordinates_comp]
  dsimp only
  rw [quotientPoints_coord, Category.assoc, C.coordinates_comp]

/-- The actual exact-weight quotient homomorphism to a standard vector group. -/
def quotientMap (d : ℕ) :
    W.groupScheme d ⟶
      VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (W.exactSupport d)) :=
  homOfPoints (fun T => W.quotientPoints T d) (W.quotientPoints_natural d)

@[simp]
theorem comp_quotientMap (d : ℕ)
    (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (W.groupScheme d).X) :
    x ≫ (W.quotientMap d).hom.hom = W.quotientPoints T d x :=
  comp_homOfPoints _ _ T x

/-- The original coordinates of a point of a represented term are extension by
zero of its own standard affine-space coordinates. -/
theorem coordinates_inclusion (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (W.groupScheme d).X) (k : Fin C.dimension) :
    C.coordinates T (x ≫ (W.inclusion d).hom.hom) k =
      if hk : k ∈ W.support d then
        (VectorGroup.coordinates (CommRingCat.of R) _ T x).toAdd
          ((W.enumeration d).symm ⟨k, hk⟩) else 0 := by
  unfold RootHeightChart.coordinates inclusion
  rw [CoordinateFiltrationTerm.inclusion_hom]
  simp only [CoordinateFiltrationTerm.schemeInclusion, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, comp_blockInclusion, blockPoints_coord]

/-- Inside the coordinate affine space of a positive-weight term, select the exact weight. -/
def selectedSupport (d : ℕ) : Set (Fin (Nat.card (W.support d))) :=
  {a | W.weight (W.enumeration d a).val = d + 1}

/-- The exact-weight root enumeration, expressed in the coordinates of the term. -/
def selectedEnumeration (d : ℕ) :
    Fin (Nat.card (W.exactSupport d)) ≃ W.selectedSupport d where
  toFun j := ⟨(W.enumeration d).symm
      ⟨(W.exactEnumeration d j).val, Nat.le_of_eq (W.exactEnumeration d j).property.symm⟩,
    by
      change W.weight ((W.enumeration d) ((W.enumeration d).symm _)).val = d + 1
      rw [Equiv.apply_symm_apply]
      exact (W.exactEnumeration d j).property⟩
  invFun a := (W.exactEnumeration d).symm
    ⟨(W.enumeration d a.val).val, a.property⟩
  left_inv j := by simp
  right_inv a := by
    apply Subtype.ext
    simp

/-- The quotient's scheme morphism is exactly ordinary coordinate projection.
Its source has a transferred group law, but the same affine-space scheme. -/
theorem quotientMap_hom (d : ℕ) :
    (W.quotientMap d).hom.hom =
      (coordinateProjection (CommRingCat.of R)
        (W.selectedSupport d) (W.selectedEnumeration d)).hom.hom := by
  apply yoneda.map_injective
  ext T x
  change x ≫ (W.quotientMap d).hom.hom =
    x ≫ (coordinateProjection (CommRingCat.of R) _ _).hom.hom
  rw [comp_quotientMap, comp_blockRestriction]
  apply VectorGroup.points_ext
  intro j
  rw [quotientPoints_coord, blockRestrictionPoints_coord, coordinates_inclusion]
  have hj : (W.exactEnumeration d j).val ∈ W.support d :=
    Nat.le_of_eq (W.exactEnumeration d j).property.symm
  rw [dite_eq_left hj]
  rfl

theorem flat_quotientMap (d : ℕ) :
    Flat (W.quotientMap d).hom.hom.left := by
  rw [quotientMap_hom]
  exact flat_coordinateProjection _ _ _

theorem surjective_quotientMap (d : ℕ) :
    Surjective (W.quotientMap d).hom.hom.left := by
  rw [quotientMap_hom]
  exact surjective_coordinateProjection _ _ _

theorem locallyOfFinitePresentation_quotientMap (d : ℕ) :
    LocallyOfFinitePresentation (W.quotientMap d).hom.hom.left := by
  rw [quotientMap_hom]
  exact locallyOfFinitePresentation_coordinateProjection _ _ _

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
