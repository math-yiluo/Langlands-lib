import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.Multiplicative
import Langlands.Group.GL.Maps

/-! # The contragredient automorphism of the actual general linear group scheme -/

noncomputable section
universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.GeneralLinear

section Matrices

variable (n : Type) [Fintype n] [DecidableEq n] (A : Type u) [CommRing A]

/-- Inverse transpose for arbitrary finite coordinate indices. -/
def matrixContragredient : GL n A ≃* GL n A :=
  let f : GL n A → GL n A := fun g =>
    { val := g.inv.transpose
      inv := g.val.transpose
      val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  { toFun := f
    invFun := f
    left_inv := by intro g; apply Units.ext; rfl
    right_inv := by intro g; apply Units.ext; rfl
    map_mul' := by
      intro g h
      apply Units.ext
      change ((h⁻¹ : GL n A).val * (g⁻¹ : GL n A).val).transpose = _
      exact Matrix.transpose_mul _ _ }

@[simp] theorem matrixContragredient_coe (g : GL n A) :
    (matrixContragredient n A g : Matrix n n A) = (g⁻¹ : GL n A).val.transpose := rfl

@[simp] theorem matrixContragredient_symm :
    (matrixContragredient n A).symm = matrixContragredient n A := rfl

@[simp] theorem matrixContragredient_involutive (g : GL n A) :
    matrixContragredient n A (matrixContragredient n A g) = g :=
  (matrixContragredient n A).left_inv g

/-- The generic coordinate formula agrees with the published finite-rank inverse transpose. -/
theorem matrixContragredient_fin (d : ℕ) :
    matrixContragredient (Fin d) A = Langlands.GeneralLinear.inverseTranspose d A := rfl

variable {A} {B : Type v} [CommRing B]

/-- Coefficient maps commute with inverse transpose. -/
theorem matrixContragredient_map (f : A →+* B) (g : GL n A) :
    matrixContragredient n B (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (matrixContragredient n A g) := by
  apply Units.ext
  rfl

/-- The inverse-transpose action preserves the coordinate evaluation pairing. -/
theorem matrixContragredient_pairing (g : GL n A) (w v : n → A) :
    ((matrixContragredient n A g : Matrix n n A) *ᵥ w) ⬝ᵥ
      ((g : Matrix n n A) *ᵥ v) = w ⬝ᵥ v := by
  rw [matrixContragredient_coe, dotProduct_comm, Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

end Matrices

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})

/-- Inverse transpose transported to the actual group of points on any test scheme. -/
def contragredientPoints (T : Over (Spec R)) :
    (T ⟶ (groupScheme n R).X) ≃* (T ⟶ (groupScheme n R).X) :=
  (pointsEquiv n R T).trans
    ((matrixContragredient n Γ(T.left, ⊤)).trans (pointsEquiv n R T).symm)

@[simp] theorem pointsEquiv_contragredientPoints (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv n R T (contragredientPoints n R T x) =
      matrixContragredient n Γ(T.left, ⊤) (pointsEquiv n R T x) :=
  (pointsEquiv n R T).apply_symm_apply _

theorem contragredientPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme n R).X) :
    contragredientPoints n R T' (a ≫ x) = a ≫ contragredientPoints n R T x := by
  apply (pointsEquiv n R T').injective
  rw [pointsEquiv_contragredientPoints, pointsEquiv_naturality,
    pointsEquiv_naturality, pointsEquiv_contragredientPoints, matrixContragredient_map]

@[simp] theorem contragredientPoints_involutive (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    contragredientPoints n R T (contragredientPoints n R T x) = x := by
  apply (pointsEquiv n R T).injective
  simp only [pointsEquiv_contragredientPoints, matrixContragredient_involutive]

/-- The actual group-scheme automorphism whose point action is inverse transpose. -/
def contragredientIso : groupScheme n R ≅ groupScheme n R :=
  isoOfPoints (contragredientPoints n R) (contragredientPoints_naturality n R)

@[simp] theorem comp_contragredientIso_hom (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    x ≫ (contragredientIso n R).hom.hom.hom = contragredientPoints n R T x :=
  comp_isoOfPoints_hom _ _ T x

/-- On global-section coordinates the scheme automorphism is inverse transpose. -/
theorem pointsEquiv_contragredientIso (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv n R T (x ≫ (contragredientIso n R).hom.hom.hom) =
      matrixContragredient n Γ(T.left, ⊤) (pointsEquiv n R T x) := by
  rw [comp_contragredientIso_hom, pointsEquiv_contragredientPoints]

/-- The contragredient morphism is an involution as a scheme morphism. -/
theorem contragredientIso_hom_comp :
    (contragredientIso n R).hom ≫ (contragredientIso n R).hom =
      𝟙 (groupScheme n R) := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_contragredientIso_hom,
    comp_contragredientIso_hom, contragredientPoints_involutive]
  change x = x ≫ 𝟙 _
  rw [Category.comp_id]

/-- The affine coordinate matrix is also inverse transpose over the test algebra itself. -/
theorem affinePointsEquiv_contragredientIso (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme n R).X) :
    affinePointsEquiv n R S (x ≫ (contragredientIso n R).hom.hom.hom) =
      matrixContragredient n S (affinePointsEquiv n R S x) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((functor n R).map (Corepresented.affineSectionsIso S).inv)).1
  change Matrix.GeneralLinearGroup.map _ _ = Matrix.GeneralLinearGroup.map _ _
  rw [← pointsEquiv_eq_affinePointsEquiv, ← matrixContragredient_map,
    ← pointsEquiv_eq_affinePointsEquiv]
  exact pointsEquiv_contragredientIso n R _ x

end Langlands.GroupScheme.GeneralLinear
