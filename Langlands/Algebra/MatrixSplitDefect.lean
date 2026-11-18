import Langlands.Algebra.MatrixGaloisSplitting
import Mathlib.RingTheory.MatrixAlgebra

/-! # Actual split presentations trivialize scalar descent defects -/

noncomputable section
universe u v w
open Matrix
open scoped TensorProduct

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.ScalarTwoCocycle

variable {Γ : Type u} [Group Γ] {A : Type v} [CommGroup A] [MulDistribMulAction Γ A]
  {E : Type w} [Group E] [MulDistribMulAction Γ E]

/-- Scalar twists of honest lifts have an actual scalar coboundary as defect. -/
theorem isCoboundary_of_scalar_twist (s : A →* E) (hinj : Function.Injective s)
    (hcentral : ∀ (a : A) (x : E), Commute (s a) x)
    (hequiv : ∀ (g : Γ) (a : A), g • s a = s (g • a))
    (x y : Γ → E) (c : Γ → Γ → A)
    (hlift : ∀ g h, x g * (g • x h) = s (c g h) * x (g * h))
    (hy : ∀ g h, y g * (g • y h) = y (g * h))
    (b : Γ → A) (hb : ∀ g, x g = s (b g) * y g) : IsCoboundary c := by
  refine ⟨b, fun g h => ?_⟩
  apply hinj
  change s (c g h) = s (b g * (g • b h) * (b (g * h))⁻¹)
  rw [map_mul, map_mul, map_inv]
  apply (eq_mul_inv_iff_mul_eq).mpr
  have hleft : x g * (g • x h) = (s (b g) * s (g • b h)) * y (g * h) := by
    rw [hb g, hb h, smul_mul', hequiv]
    calc
      _ = (s (b g) * s (g • b h)) * (y g * (g • y h)) := by
        rw [← mul_assoc, mul_assoc (s (b g)), (hcentral (g • b h) (y g)).symm.eq]
        group
      _ = _ := by rw [hy]
  have he := hlift g h
  rw [hleft, hb (g * h)] at he
  apply mul_right_cancel (b := y (g * h))
  simpa only [mul_assoc] using he.symm

end Langlands.ScalarTwoCocycle

namespace Langlands.CentralSimple.SemilinearGaloisAction

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]

attribute [local instance] coefficientGLAction

/-- An actual matrix untwisting a semilinear action supplies a scalar cochain
trivializing its chosen actual scalar defect. -/
theorem scalarDefect_isCoboundary_of_untwistingMatrix
    (ρ : SemilinearGaloisAction k L (Matrix I I L)) (Q : GL I L)
    (hQ : ∀ (σ : L ≃ₐ[k] L) (X : Matrix I I L),
      ρ.act σ ((Q : Matrix I I L) * X * ((Q⁻¹ : GL I L) : Matrix I I L)) =
        (Q : Matrix I I L) * X.map σ * ((Q⁻¹ : GL I L) : Matrix I I L)) :
    Langlands.ScalarTwoCocycle.IsCoboundary ρ.scalarDefect := by
  let y : (L ≃ₐ[k] L) → GL I L := fun σ => Q * (σ • Q)⁻¹
  have hy (σ τ : L ≃ₐ[k] L) : y σ * (σ • y τ) = y (σ * τ) := by
    simp only [y, smul_mul', smul_inv', mul_smul]
    group
  have hyact (σ : L ≃ₐ[k] L) (X : Matrix I I L) :
      ρ.act σ X = (y σ : Matrix I I L) * X.map σ * (((y σ)⁻¹ : GL I L) : Matrix I I L) := by
    have h := hQ σ (((Q⁻¹ : GL I L) : Matrix I I L) * X * (Q : Matrix I I L))
    calc
      ρ.act σ X = (Q : Matrix I I L) *
          ((((Q⁻¹ : GL I L) : Matrix I I L) * X * (Q : Matrix I I L)).map σ) *
          ((Q⁻¹ : GL I L) : Matrix I I L) := by
        simpa [Matrix.mul_assoc] using h
      _ = _ := by
        simp only [y, Matrix.map_mul, _root_.mul_inv_rev, Units.val_mul, ← smul_inv',
          coefficientGLAction_coe, _root_.inv_inv, Matrix.mul_assoc]
  have hscalar (σ : L ≃ₐ[k] L) :
      ∃ b : Lˣ, ρ.innerMatrix σ = GeneralLinearGroup.scalar I b * y σ := by
    obtain ⟨b, hb⟩ := Langlands.LinearAlgebra.SpecialLinearConjugation.exists_unit_scalar_of_conjugation_eq_conjugation
      (ρ.innerMatrix σ) (y σ) (fun g => by
        apply Units.ext
        let X := (g : Matrix I I L).map σ.symm
        have h := (ρ.act_eq_innerMatrix σ X).symm.trans (hyact σ X)
        have hmap : X.map σ = (g : Matrix I I L) := by
          ext i j
          exact σ.apply_symm_apply ((g : Matrix I I L) i j)
        rw [hmap] at h
        exact h)
    exact ⟨b, hb.trans (unit_scalar_central b (y σ)).symm.eq⟩
  choose b hb using hscalar
  exact Langlands.ScalarTwoCocycle.isCoboundary_of_scalar_twist
    (Γ := L ≃ₐ[k] L) (A := Lˣ) (E := GL I L) (GeneralLinearGroup.scalar I)
    unit_scalar_injective unit_scalar_central coefficientGLAction_scalar
    ρ.innerMatrix y ρ.scalarDefect ρ.innerMatrix_mul hy b hb

end Langlands.CentralSimple.SemilinearGaloisAction

namespace Langlands.CentralSimple

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {I : Type v} [Fintype I] [DecidableEq I]

/-- The canonical actual matrix chart for extension of matrix coefficients. -/
def matrixBaseChangeChart : L ⊗[k] Matrix I I k ≃ₐ[L] Matrix I I L where
  toRingEquiv := (matrixEquivTensor I k L).symm.toRingEquiv
  commutes' l := by
    change (matrixEquivTensor I k L).symm (l ⊗ₜ[k] (1 : Matrix I I k)) = _
    rw [matrixEquivTensor_apply_symm]
    simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem matrixBaseChangeChart_tmul (l : L) (X : Matrix I I k) :
    matrixBaseChangeChart (l ⊗ₜ[k] X) = l • X.map (algebraMap k L) :=
  matrixEquivTensor_apply_symm I k L l X

variable {A : Type u} [Ring A] [Algebra k A]

/-- An actual ground-field matrix presentation gives a canonical compatible chart
after scalar extension. -/
def splitPresentationChart (f : A ≃ₐ[k] Matrix I I k) :
    L ⊗[k] A ≃ₐ[L] Matrix I I L :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) f).trans matrixBaseChangeChart

@[simp] theorem splitPresentationChart_tmul (f : A ≃ₐ[k] Matrix I I k) (l : L) (a : A) :
    splitPresentationChart f (l ⊗ₜ[k] a) = l • (f a).map (algebraMap k L) := by
  simp [splitPresentationChart, Algebra.TensorProduct.congr_apply]

/-- The chart of a ground-field split presentation intertwines the canonical
coefficient actions on the actual tensor algebra and matrices. -/
theorem splitPresentationChart_coefficientMap (f : A ≃ₐ[k] Matrix I I k)
    (σ : L ≃ₐ[k] L) (X : L ⊗[k] A) :
    splitPresentationChart f (tensorCoefficientMap σ X) = (splitPresentationChart f X).map σ := by
  induction X with
  | tmul l a =>
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, σ.commutes]
  | add X Y hX hY =>
    simp only [map_add, hX, hY]
    ext i j
    simp

/-- An actual ground-field matrix splitting trivializes the actual scalar defect
of any supplied extension-field splitting chart of that same size. -/
theorem splittingChart_scalarDefect_isCoboundary_of_split {n : ℕ} [NeZero n]
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (f : A ≃ₐ[k] Matrix (Fin n) (Fin n) k) :
    Langlands.ScalarTwoCocycle.IsCoboundary (splittingChartAction e).scalarDefect := by
  let e0 := splitPresentationChart (L := L) f
  obtain ⟨Q, hQ⟩ := Langlands.MatrixAlgebra.exists_unit_conj_of_charts e0 e
  apply (splittingChartAction e).scalarDefect_isCoboundary_of_untwistingMatrix Q
  intro σ X
  obtain ⟨Y, rfl⟩ := e0.surjective X
  rw [← hQ, splittingChartAction_apply, hQ, splitPresentationChart_coefficientMap]

end Langlands.CentralSimple
