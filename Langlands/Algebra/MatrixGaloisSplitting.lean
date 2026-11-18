import Langlands.Algebra.SplittingChartGaloisAction
import Langlands.LinearAlgebra.GaloisVectorDescent
import Langlands.GroupScheme.SpecialLinearInnerForm.ConjugationDescent

/-! # Untwisting actual matrix descent from a scalar coboundary -/

noncomputable section
universe u v
open Matrix
open scoped TensorProduct

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CentralSimple.SemilinearGaloisAction

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {I : Type v} [Fintype I] [DecidableEq I]

attribute [local instance] coefficientGLAction

/-- Multiplying an inner matrix by a unit scalar does not change its action on
any matrix. -/
theorem scalar_mul_matrix_conjugation (a : Lˣ) (P : GL I L) (X : Matrix I I L) :
    ((GeneralLinearGroup.scalar I a * P : GL I L) : Matrix I I L) * X *
        (((GeneralLinearGroup.scalar I a * P)⁻¹ : GL I L) : Matrix I I L) =
      (P : Matrix I I L) * X * ((P⁻¹ : GL I L) : Matrix I I L) := by
  simp only [_root_.mul_inv_rev, Units.val_mul]
  have hc : Commute ((GeneralLinearGroup.scalar I a : GL I L) : Matrix I I L)
      ((P : Matrix I I L) * X * ((P⁻¹ : GL I L) : Matrix I I L)) :=
    Matrix.scalar_comm _ (Commute.all _) _
  calc
    _ = ((GeneralLinearGroup.scalar I a : GL I L) : Matrix I I L) *
        ((P : Matrix I I L) * X * ((P⁻¹ : GL I L) : Matrix I I L)) *
        (((GeneralLinearGroup.scalar I a)⁻¹ : GL I L) : Matrix I I L) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hc.eq, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

variable [FiniteDimensional k L]

/-- An actual scalar coboundary of the action's chosen inner matrices yields an
actual invertible matrix untwisting its entire semilinear action. -/
theorem exists_untwistingMatrix_of_isCoboundary
    (ρ : SemilinearGaloisAction k L (Matrix I I L))
    (hc : Langlands.ScalarTwoCocycle.IsCoboundary ρ.scalarDefect) :
    ∃ Q : GL I L, ∀ (σ : L ≃ₐ[k] L) (X : Matrix I I L),
      ρ.act σ ((Q : Matrix I I L) * X * ((Q⁻¹ : GL I L) : Matrix I I L)) =
        (Q : Matrix I I L) * X.map σ * ((Q⁻¹ : GL I L) : Matrix I I L) := by
  obtain ⟨b, hb⟩ := hc
  let y : (L ≃ₐ[k] L) → GL I L := fun σ =>
    (GeneralLinearGroup.scalar I (b σ))⁻¹ * ρ.innerMatrix σ
  have hy (σ τ : L ≃ₐ[k] L) : y σ * (σ • y τ) = y (σ * τ) :=
    Langlands.ScalarTwoCocycle.normalized_lifts_mul
      (Γ := L ≃ₐ[k] L) (A := Lˣ) (E := GL I L) (GeneralLinearGroup.scalar I)
      unit_scalar_central coefficientGLAction_scalar ρ.innerMatrix ρ.scalarDefect
      ρ.innerMatrix_mul b hb σ τ
  have hyone : y 1 = 1 := by
    apply mul_left_cancel (a := y 1)
    simpa only [one_smul, one_mul, mul_one] using hy 1 1
  have hyoneMat : (y 1 : Matrix I I L) = 1 := congrArg Units.val hyone
  have hymul (σ τ : L ≃ₐ[k] L) :
      (y (σ * τ) : Matrix I I L) = (y σ : Matrix I I L) * (y τ : Matrix I I L).map σ := by
    simpa only [Units.val_mul, coefficientGLAction_coe] using congrArg Units.val (hy σ τ).symm
  obtain ⟨Q, hQ⟩ := Langlands.LinearAlgebra.GaloisVectorDescent.exists_matrix_coboundary
    (⊤ : Subgroup (L ≃ₐ[k] L)) (fun σ => (y σ.val : Matrix I I L))
    hyoneMat (fun σ τ => hymul σ.val τ.val)
  have hQu (σ : L ≃ₐ[k] L) : y σ * (σ • Q) = Q := by
    apply Units.ext
    exact hQ ⟨σ, Subgroup.mem_top σ⟩
  have hyconj (σ : L ≃ₐ[k] L) (X : Matrix I I L) :
      ρ.act σ X = (y σ : Matrix I I L) * X.map σ * (((y σ)⁻¹ : GL I L) : Matrix I I L) := by
    rw [ρ.act_eq_innerMatrix]
    simpa only [y, map_inv] using
      (scalar_mul_matrix_conjugation ((b σ)⁻¹) (ρ.innerMatrix σ) (X.map σ)).symm
  refine ⟨Q, fun σ X => ?_⟩
  rw [hyconj]
  calc
    _ = ((y σ * (σ • Q) : GL I L) : Matrix I I L) * X.map σ *
        (((y σ * (σ • Q))⁻¹ : GL I L) : Matrix I I L) := by
      simp only [Matrix.map_mul, _root_.mul_inv_rev, Units.val_mul, ← smul_inv',
        coefficientGLAction_coe, Matrix.mul_assoc]
    _ = _ := by rw [hQu]

/-- An untwisting matrix carries ordinary base matrices into the actual fixed algebra. -/
def untwistedFixedHom (ρ : SemilinearGaloisAction k L (Matrix I I L))
    (Q : GL I L)
    (hQ : ∀ (σ : L ≃ₐ[k] L) (X : Matrix I I L),
      ρ.act σ ((Q : Matrix I I L) * X * ((Q⁻¹ : GL I L) : Matrix I I L)) =
        (Q : Matrix I I L) * X.map σ * ((Q⁻¹ : GL I L) : Matrix I I L)) :
    Matrix I I k →ₐ[k] ρ.fixed :=
  AlgHom.codRestrict
    ((Langlands.GroupScheme.SpecialLinearInnerForm.conjugationAlgHom (R := k) Q).comp
      (Algebra.ofId k L).mapMatrix) ρ.fixed (fun X σ => by
        change ρ.act σ ((Q : Matrix I I L) * X.map (algebraMap k L) *
            ((Q⁻¹ : GL I L) : Matrix I I L)) = _
        rw [hQ]
        have hmap : (X.map (algebraMap k L)).map σ = X.map (algebraMap k L) := by
          ext i j
          exact σ.commutes (X i j)
        rw [hmap]
        rfl)

omit [FiniteDimensional k L] in
/-- Untwisted base matrices embed injectively in the actual fixed algebra. -/
theorem untwistedFixedHom_injective (ρ : SemilinearGaloisAction k L (Matrix I I L))
    (Q : GL I L) (hQ) : Function.Injective (ρ.untwistedFixedHom Q hQ) := by
  intro X Y h
  have hv := congrArg Subtype.val h
  change (Q : Matrix I I L) * X.map (algebraMap k L) * ((Q⁻¹ : GL I L) : Matrix I I L) =
    (Q : Matrix I I L) * Y.map (algebraMap k L) * ((Q⁻¹ : GL I L) : Matrix I I L) at hv
  have hcancel := congrArg (fun Z : Matrix I I L =>
    ((Q⁻¹ : GL I L) : Matrix I I L) * Z * (Q : Matrix I I L)) hv
  have hm : X.map (algebraMap k L) = Y.map (algebraMap k L) := by
    simpa [Matrix.mul_assoc] using hcancel
  ext i j
  exact (algebraMap k L).injective (congrArg (fun Z : Matrix I I L => Z i j) hm)

variable [IsGalois k L]

/-- A trivial actual scalar defect constructs an actual split presentation of
the fixed matrix algebra. -/
def fixedSplitEquivOfIsCoboundary (ρ : SemilinearGaloisAction k L (Matrix I I L))
    (hc : Langlands.ScalarTwoCocycle.IsCoboundary ρ.scalarDefect) :
    Matrix I I k ≃ₐ[k] ρ.fixed := by
  let Q := (ρ.exists_untwistingMatrix_of_isCoboundary hc).choose
  have hQ := (ρ.exists_untwistingMatrix_of_isCoboundary hc).choose_spec
  let : FiniteDimensional k ρ.fixed := ρ.finiteDimensional_fixed
  have hdim : Module.finrank k (Matrix I I k) = Module.finrank k ρ.fixed := by
    calc
      Module.finrank k (Matrix I I k) = Module.finrank L (Matrix I I L) := by
        simp [Module.finrank_matrix]
      _ = Module.finrank L (L ⊗[k] ρ.fixed) := ρ.descentEquiv.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k ρ.fixed := Module.finrank_baseChange
  apply AlgEquiv.ofBijective (ρ.untwistedFixedHom Q hQ)
  exact ⟨ρ.untwistedFixedHom_injective Q hQ,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (ρ.untwistedFixedHom Q hQ).toLinearMap)).mp (ρ.untwistedFixedHom_injective Q hQ)⟩

end Langlands.CentralSimple.SemilinearGaloisAction

namespace Langlands.CentralSimple

variable {k L A : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- A coboundary of the actual scalar defect of a supplied splitting chart
constructs an actual splitting of the original algebra over its ground field. -/
theorem split_of_splittingChart_scalarDefect_isCoboundary {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (hc : Langlands.ScalarTwoCocycle.IsCoboundary (splittingChartAction e).scalarDefect) :
    Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k) :=
  ⟨(splittingChartFixedEquiv e).trans
    ((splittingChartAction e).fixedSplitEquivOfIsCoboundary hc).symm⟩

end Langlands.CentralSimple
