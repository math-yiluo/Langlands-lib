import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.Characters

/-! # An additive one-parameter subgroup through an actual vector-group point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (y : rationalPoints V)

/-- Scalar multiplication of a constant point by the additive coordinate. -/
def pointLinePoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) →* (T ⟶ V.X) where
  toFun a := (e T).symm (Multiplicative.ofAdd fun j =>
    (VectorGroup.coordinates (CommRingCat.of k) 1 T a).toAdd 0 *
      (e T (toUnit T ≫ y)).toAdd j)
  map_one' := by
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MulEquiv.apply_symm_apply, map_one, toAdd_ofAdd, toAdd_one,
      Pi.zero_apply, zero_mul]
  map_mul' a b := by
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MulEquiv.apply_symm_apply, map_mul, toAdd_ofAdd, toAdd_mul,
      Pi.add_apply, add_mul]

@[simp]
theorem pointLinePoints_coord (T : Over (Spec (CommRingCat.of k)))
    (a : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) (j : Fin n) :
    (e T (pointLinePoints e y T a)).toAdd j =
      (VectorGroup.coordinates (CommRingCat.of k) 1 T a).toAdd 0 *
        (e T (toUnit T ≫ y)).toAdd j :=
  congrArg (fun z => z.toAdd j) ((e T).apply_symm_apply _)

/-- The scalar-point family is natural on every test scheme. -/
theorem pointLinePoints_natural (he : IsNaturalVectorCoordinates e)
    {T W : Over (Spec (CommRingCat.of k))} (b : W ⟶ T)
    (a : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X) :
    pointLinePoints e y W (b ≫ a) = b ≫ pointLinePoints e y T a := by
  apply (e W).injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [pointLinePoints_coord, he T W b]
  dsimp only
  rw [pointLinePoints_coord, map_mul, VectorGroup.coordinates_comp]
  dsimp only
  have hb : b ≫ toUnit T = toUnit W := toUnit_unique _ _
  have hc := congrFun (he T W b (toUnit T ≫ y)) j
  rw [← Category.assoc, hb] at hc
  rw [hc]

/-- The actual additive-group morphism with value `y` at coordinate one. -/
def pointLineHom (he : IsNaturalVectorCoordinates e) :
    VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ V :=
  homOfPoints (pointLinePoints e y) (pointLinePoints_natural e y he)

/-- Evaluation uses coordinate one, rather than the identity coordinate zero. -/
theorem pointLineHom_at_one (he : IsNaturalVectorCoordinates e) :
    rationalPoints.map (pointLineHom e y he)
      ((VectorGroup.coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
        (Multiplicative.ofAdd (fun _ => 1))) = y := by
  change _ ≫ (pointLineHom e y he).hom.hom = y
  rw [pointLineHom, comp_homOfPoints]
  apply (e _).injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [pointLinePoints_coord, MulEquiv.apply_symm_apply]
  dsimp only [toAdd_ofAdd]
  rw [one_mul]
  have ht : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
    toUnit_unique _ _
  rw [ht, Category.id_comp]

/-- Every rational point of an actual vector group lies on an actual additive
one-parameter subgroup, with parameter value one giving the chosen point. -/
theorem IsVectorGroupOfDimension.exists_pointLine
    (hV : IsVectorGroupOfDimension V n) (y : rationalPoints V) :
    ∃ φ : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ V,
      rationalPoints.map φ
        ((VectorGroup.coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
          (Multiplicative.ofAdd (fun _ => 1))) = y := by
  obtain ⟨e, he⟩ := hV
  exact ⟨pointLineHom e y he, pointLineHom_at_one e y he⟩

end Langlands.GroupScheme.RelativeRoot
