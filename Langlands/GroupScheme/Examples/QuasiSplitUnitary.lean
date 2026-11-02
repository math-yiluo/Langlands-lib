import Langlands.Shimura.Unitary.UnitaryGroupScheme
import Langlands.Shimura.Unitary.ComplexMatrixSplitting
import Langlands.Shimura.Unitary.InvolutionBaseChangeTower
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- The antidiagonal Gram matrix of the hyperbolic hermitian plane. -/
def gram (K : Type*) [Zero K] [One K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

/-- Conjugate adjoint for the antidiagonal Gram matrix, in entry coordinates. -/
def adjoint {K : Type*} (q : K → K) (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K := !![q (M 1 1), q (M 0 1); q (M 1 0), q (M 0 0)]

theorem adjoint_eq_gram {K : Type*} [CommRing K] (q : K → K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    adjoint q M = gram K * (M.map q).transpose * gram K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjoint, gram, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The adjoint defines an algebra involution whenever conjugation does. -/
def matrixInvolution {B K : Type*} [CommRing B] [CommRing K] [Algebra B K]
    (q : K ≃ₐ[B] K) (hq : Function.Involutive q) :
    Langlands.Shimura.AlgebraInvolution B (Matrix (Fin 2) (Fin 2) K) where
  linear :=
    { toFun := adjoint q
      map_add' := by
        intro M N
        ext i j
        fin_cases i <;> fin_cases j <;> simp [adjoint]
      map_smul' := by
        intro a M
        ext i j
        fin_cases i <;> fin_cases j <;> simp [adjoint] }
  map_one := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjoint]
  map_mul M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adjoint, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  involutive M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjoint] <;> exact hq _

@[simp] theorem matrixInvolution_apply {B K : Type*} [CommRing B] [CommRing K]
    [Algebra B K] (q : K ≃ₐ[B] K) (hq : Function.Involutive q)
    (M : Matrix (Fin 2) (Fin 2) K) : matrixInvolution q hq M = adjoint q M := rfl

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]

/-- Every automorphism of a quadratic field extension squares to the identity. -/
theorem conjugation_involutive (c : E ≃ₐ[F] E) : Function.Involutive c := by
  classical
  by_cases hc : c = AlgEquiv.refl
  · subst c
    exact fun _ => rfl
  have hlo : 1 < Fintype.card (E ≃ₐ[F] E) :=
    Fintype.one_lt_card_iff.mpr ⟨c, AlgEquiv.refl, hc⟩
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
    simpa only [IsQuadraticExtension.finrank_eq_two F E] using
      (AlgEquiv.card_le (F := F) (K := E))
  have hn : Fintype.card (E ≃ₐ[F] E) = 2 := by omega
  have hp : c ^ 2 = 1 := by rw [← hn]; exact pow_card_eq_one
  intro x
  exact congrArg (fun q : E ≃ₐ[F] E => q x) hp

/-- The specified involution on the four-entry matrix algebra over E. -/
def involution (c : E ≃ₐ[F] E) :
    Langlands.Shimura.AlgebraInvolution F (Matrix (Fin 2) (Fin 2) E) :=
  matrixInvolution c (conjugation_involutive c)

theorem involution_apply (c : E ≃ₐ[F] E) (M : Matrix (Fin 2) (Fin 2) E) :
    involution c M = gram E * (M.map c).transpose * gram E := adjoint_eq_gram c M

variable {κ : Type u} [Fintype κ]

/-- U(1,1), using the existing unitary group scheme of the matrix algebra involution. -/
abbrev groupScheme (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E) :
    Langlands.GroupScheme (Spec (CommRingCat.of F)) :=
  Langlands.Shimura.AlgebraInvolution.SchemeModel.unitaryGroupScheme b (involution c)

section Points
variable (R : Type u) [CommRing R] [Algebra F R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Conjugation c tensor identity, fixing the R coefficients. -/
def scalarConjugation (c : E ≃ₐ[F] E) : E ⊗[F] R ≃ₐ[R] E ⊗[F] R :=
  (Algebra.TensorProduct.commRight F R E).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) c).trans
      (Algebra.TensorProduct.commRight F R E))

omit [IsQuadraticExtension F E] in
@[simp] theorem scalarConjugation_tmul (c : E ≃ₐ[F] E) (e : E) (r : R) :
    scalarConjugation R c (e ⊗ₜ[F] r) = c e ⊗ₜ[F] r := rfl

theorem scalarConjugation_involutive (c : E ≃ₐ[F] E) :
    Function.Involutive (scalarConjugation R c) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul e r => simp [conjugation_involutive c e]
  | add x y hx hy => simp [hx, hy]

/-- The point subgroup consists exactly of matrices satisfying the unitary equation. -/
def matrixPoints (c : E ≃ₐ[F] E) :
    Subgroup (GL (Fin 2) (E ⊗[F] R)) :=
  (matrixInvolution (scalarConjugation R c) (scalarConjugation_involutive R c)).unitary

theorem mem_matrixPoints (c : E ≃ₐ[F] E) (g : GL (Fin 2) (E ⊗[F] R)) :
    g ∈ matrixPoints R c ↔
      (g : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) * gram (E ⊗[F] R) *
        ((g : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)).map (scalarConjugation R c)).transpose *
          gram (E ⊗[F] R) = 1 := by
  rw [matrixPoints, Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
  simp only [matrixInvolution_apply, adjoint_eq_gram, Matrix.mul_assoc]

/-- Reorder scalar extension into matrices over E tensor R, with the right R action. -/
def tensorMatrixEquiv : R ⊗[F] Matrix (Fin 2) (Fin 2) E ≃ₐ[R]
    Matrix (Fin 2) (Fin 2) (E ⊗[F] R) :=
  (Langlands.Shimura.ComplexMatrix.tensorAlgEquiv F R E 2).trans
    (Algebra.TensorProduct.commRight F R E).mapMatrix

omit [IsQuadraticExtension F E] in
@[simp] theorem tensorMatrixEquiv_tmul (r : R) (M : Matrix (Fin 2) (Fin 2) E) :
    tensorMatrixEquiv R (r ⊗ₜ[F] M) = fun i j => M i j ⊗ₜ[F] r := rfl

theorem tensorMatrixEquiv_involution (c : E ≃ₐ[F] E)
    (x : R ⊗[F] Matrix (Fin 2) (Fin 2) E) :
    tensorMatrixEquiv R ((involution c).baseChange R x) =
      matrixInvolution (scalarConjugation R c) (scalarConjugation_involutive R c)
        (tensorMatrixEquiv R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [involution, matrixInvolution, adjoint, tensorMatrixEquiv_tmul]
  | add x y hx hy => simp [hx, hy]

/-- Unitary elements of the scalar-extended algebra identify with the matrix subgroup. -/
def algebraPointsEquiv (c : E ≃ₐ[F] E) :
    ((involution c).baseChange R).unitary ≃* matrixPoints R c :=
  Langlands.Shimura.AlgebraInvolution.unitaryEquiv _ _ (tensorMatrixEquiv R)
    (tensorMatrixEquiv_involution R c)

end Points

section Coefficients
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Apply an F-algebra coefficient map to the right factor of E tensor R. -/
def tensorCoefficientMap (f : R →ₐ[F] S) : E ⊗[F] R →ₐ[F] E ⊗[F] S :=
  Algebra.TensorProduct.map (AlgHom.id F E) f

omit [IsQuadraticExtension F E] in
@[simp] theorem tensorCoefficientMap_tmul (f : R →ₐ[F] S) (e : E) (r : R) :
    tensorCoefficientMap f (e ⊗ₜ[F] r) = e ⊗ₜ[F] f r := rfl

omit [IsQuadraticExtension F E] in
/-- The tensor/matrix comparison commutes with every change of coefficients. -/
theorem tensorMatrixEquiv_changeCoefficients (f : R →ₐ[F] S)
    (x : R ⊗[F] Matrix (Fin 2) (Fin 2) E) :
    tensorMatrixEquiv S (Langlands.Shimura.AlgebraInvolution.changeCoefficients f x) =
      (tensorMatrixEquiv R x).map (tensorCoefficientMap f) := by
  induction x using TensorProduct.inductionOn with
  | tmul r M => rfl
  | add x y hx hy => simp [hx, hy, Matrix.map_add]

end Coefficients

/-- Points on every test scheme, through the existing unitary-model point equivalence. -/
def pointsEquiv (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)
    (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (groupScheme b c).X) ≃*
      matrixPoints ((algΓ (CommRingCat.of F)).obj T).unop c :=
  (Langlands.Shimura.AlgebraInvolution.SchemeModel.unitaryPointsEquiv b (involution c) T).trans
    (algebraPointsEquiv _ c)

/-- Matrix coordinates of a point are the tensor/matrix image of its unitary coordinate. -/
theorem pointsEquiv_val (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E) (T : Over (Spec (CommRingCat.of F)))
    (x : T ⟶ (groupScheme b c).X) :
    ((pointsEquiv b c T x).val : Matrix (Fin 2) (Fin 2)
      (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop)) =
      tensorMatrixEquiv _ ((Langlands.Shimura.AlgebraInvolution.SchemeModel.unitaryPointsEquiv
        b (involution c) T x).val :
        ((algΓ (CommRingCat.of F)).obj T).unop ⊗[F] Matrix (Fin 2) (Fin 2) E) := rfl

/-- Restriction on any test scheme is entrywise application of the global-sections map. -/
theorem pointsEquiv_naturality (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E) {T T' : Over (Spec (CommRingCat.of F))} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme b c).X) :
    ((pointsEquiv b c T' (a ≫ x)).val : Matrix (Fin 2) (Fin 2)
      (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T').unop)) =
      (((pointsEquiv b c T x).val : Matrix (Fin 2) (Fin 2)
        (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop))).map
          (tensorCoefficientMap ((algΓ (CommRingCat.of F)).map a).unop.hom) := by
  simp only [pointsEquiv_val,
    Langlands.Shimura.AlgebraInvolution.SchemeModel.unitaryPointsEquiv_naturality]
  exact tensorMatrixEquiv_changeCoefficients _ _

end Langlands.GroupScheme.QuasiSplitUnitary
