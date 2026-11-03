import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Langlands.GroupScheme.Reductive.UnipotentQuotient

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnipotentMatrixCriterion

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {n : Type} [Fintype n] [DecidableEq n]

/-- The natural homomorphism on affine points of a coefficient representation. -/
abbrev transformation (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) :
    F ⟶ GeneralLinear.functor n R :=
  Corepresented.pointsTrans e (GeneralLinear.corepresentableBy n R) ρ

abbrev matrixPointHom (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    (S : CommAlgCat.{u} R) : F.obj S →* GL n S :=
  ((transformation e ρ).app S).hom

/-- The matrix of a representation at the universal affine point. -/
def coefficientMatrix (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) :
    Matrix n n B :=
  (matrixPointHom e ρ B (e.homEquiv (𝟙 B))).val

theorem transformation_homEquiv
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)
    {S : CommAlgCat.{u} R} (f : B ⟶ S) :
    matrixPointHom e ρ S (e.homEquiv f) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom
        (matrixPointHom e ρ B (e.homEquiv (𝟙 B))) := by
  have h := ConcreteCategory.congr_hom ((transformation e ρ).naturality f)
    (e.homEquiv (𝟙 B))
  change (transformation e ρ).app S (F.map f (e.homEquiv (𝟙 B))) =
    Matrix.GeneralLinearGroup.map f.hom.toRingHom
      ((transformation e ρ).app B (e.homEquiv (𝟙 B))) at h
  rw [← Corepresented.homEquiv_comp', Category.id_comp] at h
  exact h

theorem coefficientMatrix_groupSchemeMap (α : F ⟶ GeneralLinear.functor n R) :
    coefficientMatrix e (Corepresented.groupSchemeMap e
      (GeneralLinear.corepresentableBy n R) α) =
        ((α.app B).hom (e.homEquiv (𝟙 B))).val := by
  have h : matrixPointHom e (Corepresented.groupSchemeMap e
      (GeneralLinear.corepresentableBy n R) α) B (e.homEquiv (𝟙 B)) =
      (α.app B).hom (e.homEquiv (𝟙 B)) := by
    change Corepresented.affinePointsEquiv (GeneralLinear.functor n R)
      (GeneralLinear.corepresentableBy n R) B
      ((Corepresented.affinePointsEquiv F e B).symm (e.homEquiv (𝟙 B)) ≫
        (Corepresented.groupSchemeMap e (GeneralLinear.corepresentableBy n R) α).hom.hom) =
      (α.app B).hom (e.homEquiv (𝟙 B))
    rw [Corepresented.groupSchemeMap_affinePoints, MulEquiv.apply_symm_apply]
  exact congrArg Units.val h

theorem coefficientMatrix_toGL (a : Matrix n n B)
    (hmul : ∀ i j, Corepresented.LinearEmbedding.comulL e (a i j) =
      ∑ l, a i l ⊗ₜ[R] a l j)
    (hone : ∀ i j, Corepresented.LinearEmbedding.counitL e (a i j) =
      (1 : Matrix n n R) i j) :
    coefficientMatrix e (Corepresented.groupSchemeMap e
      (GeneralLinear.corepresentableBy n R)
      (Corepresented.LinearEmbedding.toGL e a hmul hone)) = a := by
  rw [coefficientMatrix_groupSchemeMap]
  change (e.homEquiv.symm (e.homEquiv (𝟙 B))).hom.mapMatrix a = a
  rw [Equiv.symm_apply_apply]
  rfl

theorem coefficientMatrix_comul
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) (i j : n) :
    AffineLinearEmbedding.comul e (coefficientMatrix e ρ i j) =
      ∑ l, coefficientMatrix e ρ i l ⊗ₜ[R] coefficientMatrix e ρ l j := by
  have h := congrArg (fun g : GL n (B ⊗[R] B) => g i j)
    (map_mul (matrixPointHom e ρ (Corepresented.tensorObj B B))
      (e.homEquiv (Corepresented.inl B B)) (e.homEquiv (Corepresented.inr B B)))
  rw [← Corepresented.homEquiv_comul,
    transformation_homEquiv e ρ (Corepresented.LinearEmbedding.comul e),
    transformation_homEquiv e ρ (Corepresented.inl B B),
    transformation_homEquiv e ρ (Corepresented.inr B B)] at h
  simp only [Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply] at h
  change AffineLinearEmbedding.comul e (coefficientMatrix e ρ i j) =
    ∑ l, (coefficientMatrix e ρ i l ⊗ₜ[R] (1 : B)) *
      ((1 : B) ⊗ₜ[R] coefficientMatrix e ρ l j) at h
  simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using h

theorem coefficientMatrix_counit
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) (i j : n) :
    AffineLinearEmbedding.counit e (coefficientMatrix e ρ i j) =
      (1 : Matrix n n R) i j := by
  have h := congrArg (fun g : GL n R => g i j)
    (map_one (matrixPointHom e ρ (CommAlgCat.of R R)))
  rw [← AffineLinearEmbedding.pt_homEquiv_symm e (1 : F.obj (CommAlgCat.of R R)),
    AffineLinearEmbedding.pt, transformation_homEquiv] at h
  exact h

theorem coefficientMatrix_eq_affineMatrix
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) :
    coefficientMatrix e ρ = (ρ.affineMatrix B (𝟙 _) : Matrix n n B) := by
  have h : (Corepresented.affinePointsEquiv F e B).symm (e.homEquiv (𝟙 B)) = 𝟙 _ := by
    apply (Corepresented.affinePointsEquiv F e B).injective
    rw [MulEquiv.apply_symm_apply]
    have hh := Corepresented.affinePointsEquiv_map F e B (𝟙 B)
    change (Corepresented.affinePointsEquiv F e B) ((algSpec R).map (𝟙 (op B))) =
      e.homEquiv (𝟙 B) at hh
    rw [(algSpec R).map_id] at hh
    exact hh.symm
  have hh : matrixPointHom e ρ B (e.homEquiv (𝟙 B)) = ρ.affineMatrix B (𝟙 _) := by
    change Corepresented.affinePointsEquiv (GeneralLinear.functor n R)
      (GeneralLinear.corepresentableBy n R) B
      ((Corepresented.affinePointsEquiv F e B).symm (e.homEquiv (𝟙 B)) ≫ ρ.hom.hom) =
      ρ.affineMatrix B (𝟙 _)
    rw [h]
    rfl
  exact congrArg Units.val hh

theorem scalarMap_affine (S : CommAlgCat.{u} R) (r : R) :
    scalarMap ((algSpec R).obj (op S)) r =
      (Corepresented.affineSectionsIso S).inv.hom (algebraMap R S r) := by
  exact ((Corepresented.affineSectionsIso S).inv.hom.commutes r).symm

theorem isFixedVector_iff
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) (v : n → R) :
    ρ.IsFixedVector v ↔
      ∀ i, ∑ j, v j • coefficientMatrix e ρ i j = v i • (1 : B) := by
  rw [ρ.isFixedVector_iff_universal v, coefficientMatrix_eq_affineMatrix]
  change ((ρ.pointMatrix ((algSpec R).obj (op B)) (𝟙 _) :
    Matrix n n Γ(((algSpec R).obj (op B)).left, ⊤)) *ᵥ
      (fun i => scalarMap ((algSpec R).obj (op B)) (v i)) =
        fun i => scalarMap ((algSpec R).obj (op B)) (v i)) ↔ _
  let q : B →+* Γ(((algSpec R).obj (op B)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have hq : Function.Injective q :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1
  have hs (r : R) : scalarMap ((algSpec R).obj (op B)) r = q (algebraMap R B r) :=
    scalarMap_affine B r
  rw [ρ.pointMatrix_eq_affineMatrix B (𝟙 _),
    Corepresented.affineSectionsIso_inv_ringHom]
  let a : Matrix n n B := ρ.affineMatrix B (𝟙 _)
  change ((fun i => ∑ j, q (a i j) * scalarMap ((algSpec R).obj (op B)) (v j)) =
    fun i => scalarMap ((algSpec R).obj (op B)) (v i)) ↔
      ∀ i, ∑ j, v j • a i j = v i • (1 : B)
  simp only [funext_iff, hs]
  constructor
  · intro h i
    apply hq
    simp only [Algebra.smul_def, map_sum, map_mul, mul_one]
    calc
      ∑ j, q (algebraMap R B (v j)) * q (a i j) =
          ∑ j, q (a i j) * q (algebraMap R B (v j)) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = _ := h i
  · intro h i
    have hi := congrArg q (h i)
    simp only [Algebra.smul_def, map_sum, map_mul, mul_one] at hi
    calc
      ∑ j, q (a i j) * q (algebraMap R B (v j)) =
          ∑ j, q (algebraMap R B (v j)) * q (a i j) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = _ := hi

end Langlands.GroupScheme.UnipotentMatrixCriterion
