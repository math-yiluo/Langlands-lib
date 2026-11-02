import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic
import Langlands.GroupScheme.Torus.WeilRestriction

/-! # The diagonal unitary map from the units of the quadratic algebra -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]

section Matrices
variable (R : Type u) [CommRing R] [Algebra F R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The invertible diagonal matrix with entries `a` and `c_R(a)⁻¹`. -/
def leviDiagonalMatrix (c : E ≃ₐ[F] E) (a : (E ⊗[F] R)ˣ) :
    GL (Fin 2) (E ⊗[F] R) where
  val := !![(a : E ⊗[F] R), 0; 0, scalarConjugation R c ((a⁻¹ : (E ⊗[F] R)ˣ) : E ⊗[F] R)]
  inv := !![((a⁻¹ : (E ⊗[F] R)ˣ) : E ⊗[F] R), 0; 0, scalarConjugation R c a]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← map_mul, ← Units.val_mul]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← map_mul, ← Units.val_mul]

/-- The diagonal map takes its values in the full unitary matrix group. -/
def leviDiagonalUnitary (c : E ≃ₐ[F] E) : (E ⊗[F] R)ˣ →* matrixPoints R c where
  toFun a := ⟨leviDiagonalMatrix R c a, by
    rw [matrixPoints, Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [leviDiagonalMatrix, matrixInvolution, adjoint, Matrix.mul_apply,
        Fin.sum_univ_two, ← map_mul, ← Units.val_mul]
    rw [scalarConjugation_involutive R c]
    simp⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviDiagonalMatrix]
  map_mul' a d := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [leviDiagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[simp] theorem leviDiagonalUnitary_val (c : E ≃ₐ[F] E) (a : (E ⊗[F] R)ˣ) :
    ((leviDiagonalUnitary R c a).val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) =
      !![(a : E ⊗[F] R), 0; 0,
        scalarConjugation R c ((a⁻¹ : (E ⊗[F] R)ˣ) : E ⊗[F] R)] := rfl

/-- The first diagonal entry recovers the unit parameter. -/
theorem leviDiagonalUnitary_injective (c : E ≃ₐ[F] E) :
    Function.Injective (leviDiagonalUnitary R c) := by
  intro a d h
  apply Units.ext
  exact congrArg (fun g : matrixPoints R c =>
    (g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 0 0) h

omit [IsQuadraticExtension F E] in
/-- Changing the coefficient algebra commutes with quadratic conjugation. -/
theorem tensorCoefficientMap_scalarConjugation {S : Type u} [CommRing S] [Algebra F S]
    (c : E ≃ₐ[F] E) (f : R →ₐ[F] S) (x : E ⊗[F] R) :
    tensorCoefficientMap f (scalarConjugation R c x) =
      scalarConjugation S c (tensorCoefficientMap f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul e r => rfl
  | add x y hx hy => simp [hx, hy]

/-- The diagonal unitary map is natural in every coefficient algebra. -/
theorem leviDiagonalUnitary_naturality {S : Type u} [CommRing S] [Algebra F S]
    (c : E ≃ₐ[F] E) (f : R →ₐ[F] S) (a : (E ⊗[F] R)ˣ) :
    Matrix.GeneralLinearGroup.map (tensorCoefficientMap f).toRingHom
        (leviDiagonalUnitary R c a).val =
      (leviDiagonalUnitary S c
        (Units.map (tensorCoefficientMap f).toMonoidHom a)).val := by
  apply Units.ext
  change ((leviDiagonalUnitary R c a).val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)).map _ = _
  rw [leviDiagonalUnitary_val, leviDiagonalUnitary_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorCoefficientMap_scalarConjugation, ← map_inv]

end Matrices

section Schemes
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

/-- The diagonal map on points of the represented Weil restriction. -/
def leviPoints (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (WeilGm.groupScheme (CommRingCat.of F) E).X) →*
      (T ⟶ (groupScheme b c).X) :=
  (pointsEquiv b c T).symm.toMonoidHom.comp
    ((leviDiagonalUnitary _ c).comp
      (WeilGm.pointsEquiv (CommRingCat.of F) E T).toMonoidHom)

@[simp] theorem pointsEquiv_leviPoints (T : Over (Spec (CommRingCat.of F)))
    (a : T ⟶ (WeilGm.groupScheme (CommRingCat.of F) E).X) :
    pointsEquiv b c T (leviPoints b c T a) =
      leviDiagonalUnitary ((algΓ (CommRingCat.of F)).obj T).unop c
        (WeilGm.pointsEquiv (CommRingCat.of F) E T a) :=
  MulEquiv.apply_symm_apply _ _

/-- Naturality of the diagonal map over every test scheme. -/
theorem leviPoints_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (f : T' ⟶ T) (a : T ⟶ (WeilGm.groupScheme (CommRingCat.of F) E).X) :
    leviPoints b c T' (f ≫ a) = f ≫ leviPoints b c T a := by
  apply (pointsEquiv b c T').injective
  apply Subtype.ext
  rw [pointsEquiv_leviPoints]
  apply Units.ext
  rw [pointsEquiv_naturality, pointsEquiv_leviPoints,
    WeilGm.pointsEquiv_naturality]
  exact congrArg Units.val (leviDiagonalUnitary_naturality _ c
    ((algΓ (CommRingCat.of F)).map f).unop.hom
    (WeilGm.pointsEquiv (CommRingCat.of F) E T a)).symm

/-- The Weil-restricted multiplicative group maps to the diagonal unitary subgroup. -/
def leviHom : WeilGm.groupScheme (CommRingCat.of F) E ⟶ groupScheme b c :=
  homOfPoints (leviPoints b c) (leviPoints_naturality b c)

/-- On all test schemes, the Levi homomorphism is `a ↦ diag(a,c_R(a)⁻¹)`. -/
@[simp] theorem pointsEquiv_leviHom (T : Over (Spec (CommRingCat.of F)))
    (a : T ⟶ (WeilGm.groupScheme (CommRingCat.of F) E).X) :
    pointsEquiv b c T (a ≫ (leviHom b c).hom.hom) =
      leviDiagonalUnitary ((algΓ (CommRingCat.of F)).obj T).unop c
        (WeilGm.pointsEquiv (CommRingCat.of F) E T a) := by
  rw [leviHom, comp_homOfPoints, pointsEquiv_leviPoints]

end Schemes
end Langlands.GroupScheme.QuasiSplitUnitary
