import Langlands.LinearAlgebra.NumberFieldQuadraticIsotropyStatement
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Diagonal coordinates for quadratic isotropy -/

noncomputable section

universe u

open QuadraticMap
open scoped TensorProduct

namespace Langlands

/-- Local-to-global isotropy for diagonal forms with nonzero coefficients. -/
def NumberFieldDiagonalQuadraticIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (w : Fin n → F),
    (∀ i, w i ≠ 0) →
    (∀ v : Global.Place F, ¬ (weightedSumSquares (Global.placeCompletion F v)
      (fun i => algebraMap F (Global.placeCompletion F v) (w i))).Anisotropic) →
    ¬ (weightedSumSquares F w).Anisotropic

namespace QuadraticIsotropy

section ScalarExtension

variable {F V ι : Type*} [CommRing F] [Invertible (2 : F)] [Fintype ι]
  [AddCommGroup V] [Module F V] (A : Type*) [CommRing A] [Algebra F A]

/-- The scalar extension of a diagonally represented form is isometric to the
diagonal form with extended coefficients. -/
def weightedSumSquaresScalarExtension {q : QuadraticForm F V} {w : ι → F}
    (e : q.IsometryEquiv (weightedSumSquares F w)) :
    (q.baseChange A).IsometryEquiv (weightedSumSquares A (fun i => algebraMap F A (w i))) := by
  classical
  let f := (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e.toLinearEquiv).trans
    (TensorProduct.piScalarRight F A A ι)
  let r := weightedSumSquares A (fun i => algebraMap F A (w i))
  refine ⟨f, fun z => ?_⟩
  have h : r.comp f.toLinearMap = q.baseChange A := by
    apply baseChange_ext
    intro x
    change r (f (1 ⊗ₜ[F] x)) = q.baseChange A (1 ⊗ₜ[F] x)
    have hf : f (1 ⊗ₜ[F] x) = fun i => algebraMap F A (e x i) := by
      ext i
      simp [f, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Algebra.smul_def]
    rw [hf, QuadraticForm.baseChange_tmul, ← e.map_app x]
    simp only [r, weightedSumSquares_apply, Algebra.smul_def, Algebra.algebraMap_self_apply,
      mul_one, map_sum, map_mul]
  exact DFunLike.congr_fun h z

end ScalarExtension

/-- An isometry carries a nonzero zero to a nonzero zero. -/
theorem isotropic_of_isometryEquiv {F V W : Type*} [CommRing F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {q : QuadraticForm F V} {r : QuadraticForm F W}
    (e : q.IsometryEquiv r) (h : ¬ q.Anisotropic) : ¬ r.Anisotropic := by
  obtain ⟨x, hx, hz⟩ := (not_anisotropic_iff_exists _).mp h
  exact (not_anisotropic_iff_exists _).mpr
    ⟨e x, fun he => hx (e.toLinearEquiv.injective (he.trans (map_zero e).symm)),
      (e.map_app x).trans hz⟩

end QuadraticIsotropy

/-- Diagonal local-to-global isotropy gives the corresponding result on arbitrary
finite-dimensional spaces by an orthogonal basis and scalar extension. -/
theorem numberFieldQuadraticIsotropy_of_diagonal
    (diagonal : NumberFieldDiagonalQuadraticIsotropyStatement.{u}) :
    NumberFieldQuadraticIsotropyStatement.{u} := by
  intro F _ _ V _ _ _ q hq hloc
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  have hsep : (associated (R := F) q).SeparatingLeft := by
    intro x hx
    apply hq.1 x
    intro y
    rw [← two_nsmul_associated F q]
    simp only [LinearMap.smul_apply, hx y, smul_zero]
  obtain ⟨w, ⟨e⟩⟩ := q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  let a : Fin (Module.finrank F V) → F := fun i => w i
  change q.IsometryEquiv (weightedSumSquares F a) at e
  apply QuadraticIsotropy.isotropic_of_isometryEquiv e.symm
  apply diagonal F _ a (fun i => (w i).ne_zero)
  intro v
  exact QuadraticIsotropy.isotropic_of_isometryEquiv
    (QuadraticIsotropy.weightedSumSquaresScalarExtension (Global.placeCompletion F v) e)
    (hloc v)

end Langlands
