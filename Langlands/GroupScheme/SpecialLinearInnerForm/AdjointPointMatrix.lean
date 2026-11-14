import Langlands.GroupScheme.SpecialLinearInnerForm.AdjointMatrix
import Langlands.Algebra.MatrixAlgEquivInnerProof
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Field matrices for the adjoint action on the special linear group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearInnerForm

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n]
  {M A : GroupScheme (Spec (CommRingCat.of K))} {q : M ⟶ A}

/-- The algebra action of an adjoint point is invertible, with inverse given by
its inverse point. -/
def adjointMatrixEquiv (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c : matrixTest (K := K) L ⟶ A.X) :
    Matrix n n L ≃ₐ[L] Matrix n n L :=
  AlgEquiv.ofAlgHom (adjointMatrixHom hq i c) (adjointMatrixHom hq i c⁻¹)
    (by
      apply AlgHom.ext
      intro X
      change adjointMatrixHom hq i c (adjointMatrixHom hq i c⁻¹ X) = X
      rw [← adjointMatrixHom_mul, mul_inv_cancel, adjointMatrixHom_one]
      rfl)
    (by
      apply AlgHom.ext
      intro X
      change adjointMatrixHom hq i c⁻¹ (adjointMatrixHom hq i c X) = X
      rw [← adjointMatrixHom_mul, inv_mul_cancel, adjointMatrixHom_one]
      rfl)

/-- A field-valued adjoint point acts on every test by conjugation by one
matrix over that field, pulled back along the test's coefficient map. -/
theorem exists_matrix_for_adjoint_point (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    (c : matrixTest (K := K) K ⟶ A.X) :
    ∃ x : Matrix.GeneralLinearGroup n K,
      ∀ (V : Over (Spec (CommRingCat.of K)))
        (s : V ⟶ matrixTest (K := K) K) (g : V ⟶ M.X),
        (pointMatrix i V (hq.innerAction.act (s ≫ c) g) : Matrix n n Γ(V.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (sectionMap s) x : Matrix n n Γ(V.left, ⊤)) *
            (pointMatrix i V g : Matrix n n Γ(V.left, ⊤)) *
            (Matrix.GeneralLinearGroup.map (sectionMap s) x⁻¹ :
              Matrix n n Γ(V.left, ⊤)) := by
  obtain ⟨x, hx⟩ := Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv
    (adjointMatrixEquiv hq i c)
  refine ⟨x, fun V s g => ?_⟩
  rw [pointMatrix_innerAction]
  have he : extendMatrix (sectionMap s) (adjointMatrixHom hq i c).toLinearMap =
      (conjugationAlgHom (R := Γ(V.left, ⊤))
        (Matrix.GeneralLinearGroup.map (sectionMap s) x)).toLinearMap := by
    apply extendMatrix_eq
    intro X
    have h := hx X
    change adjointMatrixHom hq i c X = _ at h
    change _ = (adjointMatrixHom hq i c X).map (sectionMap s)
    rw [h, Matrix.map_mul, Matrix.map_mul]
    rfl
  rw [he]
  rfl

/-- The affine test associated to the field itself is the terminal base test. -/
def matrixBaseIso : matrixTest (K := K) K ≅ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (Spec (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K K))
    simp)

/-- Pullback of field coefficients along the terminal test map is the structure
map on global sections. -/
theorem sectionMap_matrixBase (V : Over (Spec (CommRingCat.of K))) :
    sectionMap (Over.homMk V.hom (by simp) ≫ (matrixBaseIso (K := K)).inv) =
      scalarMap V := by
  rfl

/-- Every ground-field adjoint point has a single matrix describing the
corresponding group-scheme automorphism on all tests. -/
theorem exists_matrix_for_adjoint_basePoint (hq : IsAdjointQuotient q)
    (i : M ≅ SpecialLinear.groupScheme n (CommRingCat.of K))
    (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    ∃ x : Matrix.GeneralLinearGroup n K,
      ∀ (V : Over (Spec (CommRingCat.of K))) (g : V ⟶ M.X),
        (pointMatrix i V (g ≫ (hq.innerAction.basePointIso c).hom.hom.hom) :
            Matrix n n Γ(V.left, ⊤)) =
          (Matrix.GeneralLinearGroup.map (scalarMap V) x : Matrix n n Γ(V.left, ⊤)) *
            (pointMatrix i V g : Matrix n n Γ(V.left, ⊤)) *
            (Matrix.GeneralLinearGroup.map (scalarMap V) x⁻¹ :
              Matrix n n Γ(V.left, ⊤)) := by
  obtain ⟨x, hx⟩ := exists_matrix_for_adjoint_point hq i ((matrixBaseIso (K := K)).hom ≫ c)
  refine ⟨x, fun V g => ?_⟩
  rw [AutomorphicAction.comp_basePointIso_hom]
  have h := hx V (Over.homMk V.hom (by simp) ≫ (matrixBaseIso (K := K)).inv) g
  rw [sectionMap_matrixBase] at h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, constantPoint] using h

end Langlands.GroupScheme.SpecialLinearInnerForm
