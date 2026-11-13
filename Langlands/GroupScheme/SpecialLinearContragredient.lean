import Langlands.GroupScheme.Reductive.SpecialLinearTorus
import Langlands.GroupScheme.GeneralLinearContragredient

/-! # The contragredient automorphism of the actual special linear group scheme -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

section Matrices

variable (n : Type) [Fintype n] [DecidableEq n] (A : Type u) [CommRing A]

variable {n A} in
/-- Transpose reverses products of determinant-one matrices. -/
theorem transpose_mul_eq (g h : Matrix.SpecialLinearGroup n A) :
    Matrix.SpecialLinearGroup.transpose (g * h) =
      Matrix.SpecialLinearGroup.transpose h * Matrix.SpecialLinearGroup.transpose g := by
  ext i j
  change ((g : Matrix n n A) * (h : Matrix n n A)).transpose i j =
    ((h : Matrix n n A).transpose * (g : Matrix n n A).transpose) i j
  rw [Matrix.transpose_mul]

variable {n A} in
/-- Transpose commutes with the (adjugate) inverse of a determinant-one matrix. -/
theorem transpose_inv_eq (g : Matrix.SpecialLinearGroup n A) :
    Matrix.SpecialLinearGroup.transpose g⁻¹ = (Matrix.SpecialLinearGroup.transpose g)⁻¹ := by
  ext i j
  change (Matrix.adjugate (g : Matrix n n A)).transpose i j =
    Matrix.adjugate (g : Matrix n n A).transpose i j
  rw [Matrix.adjugate_transpose]

variable {n A} in
/-- Transposing twice is the identity on determinant-one matrices. -/
theorem transpose_transpose_eq (g : Matrix.SpecialLinearGroup n A) :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose g) = g := by
  ext i j
  rfl

/-- Inverse transpose `g ↦ (g⁻¹)ᵀ` on determinant-one matrices, for arbitrary finite
coordinate indices and any commutative ring. -/
def matrixContragredient :
    Matrix.SpecialLinearGroup n A ≃* Matrix.SpecialLinearGroup n A :=
  let f : Matrix.SpecialLinearGroup n A → Matrix.SpecialLinearGroup n A :=
    fun g => Matrix.SpecialLinearGroup.transpose g⁻¹
  have hf : ∀ g, f (f g) = g := by
    intro g
    change Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose g⁻¹)⁻¹ = g
    rw [← transpose_inv_eq, inv_inv, transpose_transpose_eq]
  { toFun := f
    invFun := f
    left_inv := hf
    right_inv := hf
    map_mul' := by
      intro g h
      change Matrix.SpecialLinearGroup.transpose (g * h)⁻¹ =
        Matrix.SpecialLinearGroup.transpose g⁻¹ * Matrix.SpecialLinearGroup.transpose h⁻¹
      rw [mul_inv_rev, transpose_mul_eq] }

theorem matrixContragredient_apply (g : Matrix.SpecialLinearGroup n A) :
    matrixContragredient n A g = Matrix.SpecialLinearGroup.transpose g⁻¹ := rfl

/-- The underlying matrix of the contragredient is the transpose of the inverse. -/
@[simp] theorem matrixContragredient_coe (g : Matrix.SpecialLinearGroup n A) :
    (matrixContragredient n A g : Matrix n n A) =
      ((g⁻¹ : Matrix.SpecialLinearGroup n A) : Matrix n n A).transpose := rfl

/-- The underlying matrix of the contragredient is the transposed adjugate. -/
theorem matrixContragredient_coe_eq_adjugate (g : Matrix.SpecialLinearGroup n A) :
    (matrixContragredient n A g : Matrix n n A) =
      (Matrix.adjugate (g : Matrix n n A)).transpose := rfl

@[simp] theorem matrixContragredient_symm :
    (matrixContragredient n A).symm = matrixContragredient n A := rfl

@[simp] theorem matrixContragredient_involutive (g : Matrix.SpecialLinearGroup n A) :
    matrixContragredient n A (matrixContragredient n A g) = g :=
  (matrixContragredient n A).left_inv g

/-- In `GL`, the special-linear contragredient is the published general-linear one. -/
theorem toGL_matrixContragredient (g : Matrix.SpecialLinearGroup n A) :
    Matrix.SpecialLinearGroup.toGL (matrixContragredient n A g) =
      GeneralLinear.matrixContragredient n A (Matrix.SpecialLinearGroup.toGL g) := by
  apply Units.ext
  rw [GeneralLinear.matrixContragredient_coe, ← map_inv]
  rfl

variable {A} {B : Type v} [CommRing B]

/-- Coefficient maps commute with inverse transpose. -/
theorem matrixContragredient_map (f : A →+* B) (g : Matrix.SpecialLinearGroup n A) :
    matrixContragredient n B (Matrix.SpecialLinearGroup.map f g) =
      Matrix.SpecialLinearGroup.map f (matrixContragredient n A g) := by
  rw [matrixContragredient_apply, matrixContragredient_apply, ← map_inv]
  ext i j
  rfl

end Matrices

section Scheme

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

/-- The actual group-scheme automorphism of `SL_n` whose point action on every test scheme is
inverse transpose. -/
def contragredientIso : groupScheme n R ≅ groupScheme n R :=
  isoOfPoints (contragredientPoints n R) (contragredientPoints_naturality n R)

@[simp] theorem comp_contragredientIso_hom (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    x ≫ (contragredientIso n R).hom.hom.hom = contragredientPoints n R T x :=
  comp_isoOfPoints_hom _ _ T x

/-- On global-section coordinates the scheme automorphism is inverse transpose, as an
equality of determinant-one matrices. -/
theorem pointsEquiv_contragredientIso' (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv n R T (x ≫ (contragredientIso n R).hom.hom.hom) =
      matrixContragredient n Γ(T.left, ⊤) (pointsEquiv n R T x) := by
  rw [comp_contragredientIso_hom, pointsEquiv_contragredientPoints]

/-- On global-section coordinates the scheme automorphism is inverse transpose: the matrix of
the image point is the transpose of the matrix of the inverse point. -/
theorem pointsEquiv_contragredientIso (T : Over (Spec R))
    (x : T ⟶ (groupScheme n R).X) :
    ((pointsEquiv n R T (x ≫ (contragredientIso n R).hom.hom.hom) :
        Matrix.SpecialLinearGroup n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤)) =
      (((pointsEquiv n R T x)⁻¹ : Matrix.SpecialLinearGroup n Γ(T.left, ⊤)) :
        Matrix n n Γ(T.left, ⊤)).transpose := by
  rw [pointsEquiv_contragredientIso', matrixContragredient_coe]

/-- The contragredient morphism is an involution as a group-scheme morphism. -/
theorem contragredientIso_hom_comp_hom :
    (contragredientIso n R).hom ≫ (contragredientIso n R).hom = 𝟙 (groupScheme n R) := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_contragredientIso_hom,
    comp_contragredientIso_hom, contragredientPoints_involutive]
  change x = x ≫ 𝟙 _
  rw [Category.comp_id]

/-- The inverse of the contragredient isomorphism is its forward morphism. -/
theorem contragredientIso_inv :
    (contragredientIso n R).inv = (contragredientIso n R).hom := by
  rw [← Category.comp_id (contragredientIso n R).inv, ← contragredientIso_hom_comp_hom,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The inclusion `SL_n ⟶ GL_n` intertwines the special-linear and general-linear
contragredient automorphisms. -/
theorem contragredientIso_hom_comp_inclusion :
    (contragredientIso n R).hom ≫ inclusion n R =
      inclusion n R ≫ (GeneralLinear.contragredientIso n R).hom := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc]
  apply (GeneralLinear.pointsEquiv n R T).injective
  rw [pointsEquiv_inclusion, GeneralLinear.pointsEquiv_contragredientIso, pointsEquiv_inclusion,
    pointsEquiv_contragredientIso', toGL_matrixContragredient]

end Scheme

namespace FinSucc

section Torus

/-- The torus matrix of the inverse family is the inverse torus matrix. -/
theorem torusMatrix_inv {n : ℕ} {A : Type*} [CommRing A] (τ : ULift.{u} (Fin n) → Aˣ) :
    torusMatrix τ⁻¹ = (torusMatrix τ)⁻¹ :=
  map_inv (torusMatrixHom n A) τ

/-- Inverse transpose sends the torus matrix of `τ` to the torus matrix of `τ⁻¹`. -/
theorem matrixContragredient_torusMatrix {n : ℕ} {A : Type u} [CommRing A]
    (τ : ULift.{u} (Fin n) → Aˣ) :
    matrixContragredient (Fin (n + 1)) A (torusMatrix τ) = torusMatrix τ⁻¹ := by
  rw [matrixContragredient_apply, ← torusMatrix_inv]
  ext i j
  change (torusMatrix τ⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) A).transpose i j =
    (torusMatrix τ⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i j
  rw [coe_torusMatrix, Matrix.diagonal_transpose]

variable (n : ℕ) (R : CommRingCat.{u})

/-- The contragredient automorphism of `SL_{n+1}` restricts on the diagonal torus to inversion:
composing the diagonal torus with it equals composing the negation endomorphism `-𝟙` of the
split torus (in the additive Hom group of commutative group schemes) with the diagonal torus. -/
theorem diagonalTorus_comp_contragredientIso_hom :
    diagonalTorus n R ≫ (contragredientIso (Fin (n + 1)) R).hom =
      CommGroupScheme.groupHom (-𝟙 (splitTorus.commGroupScheme (Spec R) (ULift.{u} (Fin n)))) ≫
        diagonalTorus n R := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc]
  have hneg : x ≫ (CommGroupScheme.groupHom
      (-𝟙 (splitTorus.commGroupScheme (Spec R) (ULift.{u} (Fin n))))).hom.hom = x⁻¹ := by
    rw [← neg_one_zsmul, comp_groupHom_zsmul, zpow_neg_one]
    congr 1
  rw [hneg]
  apply (pointsEquiv (Fin (n + 1)) R T).injective
  rw [pointsEquiv_contragredientIso', pointsEquiv_diagonalTorus, pointsEquiv_diagonalTorus,
    map_inv, matrixContragredient_torusMatrix]

end Torus

end FinSucc

end Langlands.GroupScheme.SpecialLinear
