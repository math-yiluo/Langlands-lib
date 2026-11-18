import Langlands.Algebra.TensorProductSplittingCharts

/-! # Scalar defects of actual tensor-cube splitting charts -/

noncomputable section
universe u v w
open Matrix
open scoped TensorProduct Kronecker

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.ScalarTwoCocycle

variable {Γ : Type u} [Group Γ] {A : Type v} [CommGroup A] [MulDistribMulAction Γ A]
  {E : Type w} [Group E] [MulDistribMulAction Γ E]

/-- Triviality of a scalar defect transfers across actual scalar comparison of lifts. -/
theorem isCoboundary_of_scalar_comparison (s : A →* E) (hinj : Function.Injective s)
    (hcentral : ∀ (a : A) (x : E), Commute (s a) x)
    (hequiv : ∀ (g : Γ) (a : A), g • s a = s (g • a))
    (x y : Γ → E) (c d : Γ → Γ → A)
    (hx : ∀ g h, x g * (g • x h) = s (c g h) * x (g * h))
    (hy : ∀ g h, y g * (g • y h) = s (d g h) * y (g * h))
    (hcompare : ∀ g, ∃ b : A, x g = s b * y g) (hd : IsCoboundary d) :
    IsCoboundary c := by
  obtain ⟨a, ha⟩ := hd
  choose b hb using hcompare
  let z : Γ → E := fun g => (s (a g))⁻¹ * y g
  have hz (g h : Γ) : z g * (g • z h) = z (g * h) :=
    normalized_lifts_mul (Γ := Γ) (A := A) (E := E) s hcentral hequiv y d hy a ha g h
  have hxz (g : Γ) : x g = s (b g * a g) * z g := by
    rw [hb, map_mul]
    dsimp [z]
    group
  exact isCoboundary_of_scalar_twist s hinj hcentral hequiv x z c hx hz
    (fun g => b g * a g) hxz

end Langlands.ScalarTwoCocycle

namespace Langlands.CentralSimple.SemilinearGaloisAction

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]

attribute [local instance] coefficientGLAction

/-- Actual invertible lifts with identical matrix conjugation actions have
simultaneously trivial scalar defects. -/
theorem isCoboundary_of_same_matrix_conjugation
    (x y : (L ≃ₐ[k] L) → GL I L) (c d : (L ≃ₐ[k] L) → (L ≃ₐ[k] L) → Lˣ)
    (hx : ∀ σ τ, x σ * (σ • x τ) = GeneralLinearGroup.scalar I (c σ τ) * x (σ * τ))
    (hy : ∀ σ τ, y σ * (σ • y τ) = GeneralLinearGroup.scalar I (d σ τ) * y (σ * τ))
    (hconj : ∀ (σ : L ≃ₐ[k] L) (X : Matrix I I L),
      (x σ : Matrix I I L) * X * (((x σ)⁻¹ : GL I L) : Matrix I I L) =
        (y σ : Matrix I I L) * X * (((y σ)⁻¹ : GL I L) : Matrix I I L))
    (hd : Langlands.ScalarTwoCocycle.IsCoboundary d) :
    Langlands.ScalarTwoCocycle.IsCoboundary c := by
  have hcompare (σ : L ≃ₐ[k] L) : ∃ b : Lˣ, x σ = GeneralLinearGroup.scalar I b * y σ := by
    obtain ⟨b, hb⟩ := Langlands.LinearAlgebra.SpecialLinearConjugation.exists_unit_scalar_of_conjugation_eq_conjugation
      (x σ) (y σ) (fun g => by apply Units.ext; exact hconj σ (g : Matrix I I L))
    exact ⟨b, hb.trans (unit_scalar_central b (y σ)).symm.eq⟩
  exact Langlands.ScalarTwoCocycle.isCoboundary_of_scalar_comparison
    (Γ := L ≃ₐ[k] L) (A := Lˣ) (E := GL I L) (GeneralLinearGroup.scalar I)
    unit_scalar_injective unit_scalar_central coefficientGLAction_scalar x y c d hx hy hcompare hd

end Langlands.CentralSimple.SemilinearGaloisAction

namespace Langlands.CentralSimple.SemilinearGaloisAction

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {I : Type v} [Fintype I] [DecidableEq I]
  {J : Type w} [Fintype J] [DecidableEq J]

attribute [local instance] coefficientGLAction

/-- Prescribed projective lift families multiply their scalar defects under the
actual invertible Kronecker product. -/
theorem kronecker_lifts_mul
    (x : (L ≃ₐ[k] L) → GL I L) (y : (L ≃ₐ[k] L) → GL J L)
    (c d : (L ≃ₐ[k] L) → (L ≃ₐ[k] L) → Lˣ)
    (hx : ∀ σ τ, x σ * (σ • x τ) = GeneralLinearGroup.scalar I (c σ τ) * x (σ * τ))
    (hy : ∀ σ τ, y σ * (σ • y τ) = GeneralLinearGroup.scalar J (d σ τ) * y (σ * τ))
    (σ τ : L ≃ₐ[k] L) :
    (x σ).kronecker (y σ) * (σ • (x τ).kronecker (y τ)) =
      GeneralLinearGroup.scalar (I × J) (c σ τ * d σ τ) *
        (x (σ * τ)).kronecker (y (σ * τ)) := by
  rw [coefficientGLAction_kronecker, ← kroneckerGL_mul, hx, hy,
    kroneckerGL_mul, scalar_kroneckerGL_scalar]

end Langlands.CentralSimple.SemilinearGaloisAction

namespace Langlands.CentralSimple

variable {k L A B : Type u} [Field k] [Field L] [Algebra k L]
  [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {I : Type v} [Fintype I] [DecidableEq I]
  {J : Type w} [Fintype J] [DecidableEq J]

/-- Actual inner lifts of the two chart actions give actual inner lifts of the
tensor chart action on every matrix. -/
theorem tensorSplittingChart_act_eq_kronecker
    (eA : L ⊗[k] A ≃ₐ[L] Matrix I I L) (eB : L ⊗[k] B ≃ₐ[L] Matrix J J L)
    (x : (L ≃ₐ[k] L) → GL I L) (y : (L ≃ₐ[k] L) → GL J L)
    (hx : ∀ (σ : L ≃ₐ[k] L) (X : Matrix I I L),
      (splittingChartIndexAction eA).act σ X =
        (x σ : Matrix I I L) * X.map σ * (((x σ)⁻¹ : GL I L) : Matrix I I L))
    (hy : ∀ (σ : L ≃ₐ[k] L) (Y : Matrix J J L),
      (splittingChartIndexAction eB).act σ Y =
        (y σ : Matrix J J L) * Y.map σ * (((y σ)⁻¹ : GL J L) : Matrix J J L))
    (σ : L ≃ₐ[k] L) (Z : Matrix (I × J) (I × J) L) :
    (splittingChartIndexAction (tensorSplittingChart eA eB)).act σ Z =
      ((x σ).kronecker (y σ) : Matrix (I × J) (I × J) L) * Z.map σ *
        ((((x σ).kronecker (y σ))⁻¹ : GL (I × J) L) : Matrix (I × J) (I × J) L) := by
  obtain ⟨T, rfl⟩ := (Matrix.kroneckerAlgEquiv I J L).surjective Z
  induction T with
  | tmul X Y =>
    simp only [Matrix.kroneckerAlgEquiv_apply, kroneckerLinearEquiv_tmul]
    rw [tensorSplittingChart_action_kronecker, hx, hy]
    have hmap : (X ⊗ₖ Y).map σ = X.map σ ⊗ₖ Y.map σ := by
      ext ⟨i, j⟩ ⟨i', j'⟩
      exact map_mul σ (X i i') (Y j j')
    rw [hmap]
    change _ = (((x σ : Matrix I I L) ⊗ₖ (y σ : Matrix J J L)) *
      (X.map σ ⊗ₖ Y.map σ)) *
      ((((x σ)⁻¹ : GL I L) : Matrix I I L) ⊗ₖ (((y σ)⁻¹ : GL J L) : Matrix J J L))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  | add T U hT hU =>
    simp only [map_add, hT, hU, Matrix.map_add σ (map_add σ), Matrix.mul_add, Matrix.add_mul]

/-- Any actual ground-field splitting trivializes the scalar defect of the
arbitrary-index chart action. -/
theorem splittingChartIndex_scalarDefect_isCoboundary_of_split [Nonempty I]
    (e : L ⊗[k] A ≃ₐ[L] Matrix I I L) (f : A ≃ₐ[k] Matrix I I k) :
    Langlands.ScalarTwoCocycle.IsCoboundary (splittingChartIndexAction e).scalarDefect := by
  let e0 := splitPresentationChart (L := L) f
  obtain ⟨Q, hQ⟩ := Langlands.MatrixAlgebra.exists_unit_conj_of_charts e0 e
  apply (splittingChartIndexAction e).scalarDefect_isCoboundary_of_untwistingMatrix Q
  intro σ X
  obtain ⟨Y, rfl⟩ := e0.surjective X
  rw [← hQ, splittingChartIndexAction_apply, hQ, splitPresentationChart_coefficientMap]

end Langlands.CentralSimple

namespace Langlands.CentralSimple

variable {k L A : Type u} [Field k] [Field L] [Algebra k L] [Ring A] [Algebra k A]
  {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]

attribute [local instance] SemilinearGaloisAction.coefficientGLAction

/-- An actual splitting trivializes the defect of any prescribed actual lifts
of its chart action. -/
theorem splittingChartIndex_prescribedDefect_isCoboundary_of_split
    (e : L ⊗[k] A ≃ₐ[L] Matrix I I L) (f : A ≃ₐ[k] Matrix I I k)
    (x : (L ≃ₐ[k] L) → GL I L) (c : (L ≃ₐ[k] L) → (L ≃ₐ[k] L) → Lˣ)
    (hact : ∀ (σ : L ≃ₐ[k] L) (X : Matrix I I L),
      (splittingChartIndexAction e).act σ X =
        (x σ : Matrix I I L) * X.map σ * (((x σ)⁻¹ : GL I L) : Matrix I I L))
    (hlift : ∀ σ τ, x σ * (σ • x τ) = GeneralLinearGroup.scalar I (c σ τ) * x (σ * τ)) :
    Langlands.ScalarTwoCocycle.IsCoboundary c := by
  let ρ := splittingChartIndexAction e
  apply SemilinearGaloisAction.isCoboundary_of_same_matrix_conjugation
    x ρ.innerMatrix c ρ.scalarDefect hlift ρ.innerMatrix_mul
    _ (splittingChartIndex_scalarDefect_isCoboundary_of_split e f)
  intro σ X
  let Y := X.map σ.symm
  have h := (hact σ Y).symm.trans (ρ.act_eq_innerMatrix σ Y)
  have hmap : Y.map σ = X := by
    ext i j
    exact σ.apply_symm_apply (X i j)
  rw [hmap] at h
  exact h

/-- The precise proposition implemented by `splittingChart_scalarDefect_cube_isCoboundary_of_tensorCube_split`. -/
def TensorCubeScalarDefectCoboundaryStatement : Prop :=
  ∀ (e : L ⊗[k] A ≃ₐ[L] Matrix I I L)
    (_f : (A ⊗[k] A) ⊗[k] A ≃ₐ[k] Matrix ((I × I) × I) ((I × I) × I) k),
    Langlands.ScalarTwoCocycle.IsCoboundary
      (fun σ τ => (splittingChartIndexAction e).scalarDefect σ τ ^ 3)

/-- An actual splitting of the tensor cube supplies a cochain killing the cube
of the actual scalar defect of the original splitting chart. -/
theorem splittingChart_scalarDefect_cube_isCoboundary_of_tensorCube_split
    (e : L ⊗[k] A ≃ₐ[L] Matrix I I L)
    (f : (A ⊗[k] A) ⊗[k] A ≃ₐ[k] Matrix ((I × I) × I) ((I × I) × I) k) :
    Langlands.ScalarTwoCocycle.IsCoboundary
      (fun σ τ => (splittingChartIndexAction e).scalarDefect σ τ ^ 3) := by
  let ρ := splittingChartIndexAction e
  let x₂ : (L ≃ₐ[k] L) → GL (I × I) L :=
    fun σ => (ρ.innerMatrix σ).kronecker (ρ.innerMatrix σ)
  let c₂ : (L ≃ₐ[k] L) → (L ≃ₐ[k] L) → Lˣ :=
    fun σ τ => ρ.scalarDefect σ τ * ρ.scalarDefect σ τ
  have h₂ : ∀ σ τ, x₂ σ * (σ • x₂ τ) =
      GeneralLinearGroup.scalar (I × I) (c₂ σ τ) * x₂ (σ * τ) :=
    SemilinearGaloisAction.kronecker_lifts_mul
      ρ.innerMatrix ρ.innerMatrix ρ.scalarDefect ρ.scalarDefect
      ρ.innerMatrix_mul ρ.innerMatrix_mul
  have ha₂ := tensorSplittingChart_act_eq_kronecker e e
    ρ.innerMatrix ρ.innerMatrix ρ.act_eq_innerMatrix ρ.act_eq_innerMatrix
  let e₂ := tensorSplittingChart e e
  let x₃ : (L ≃ₐ[k] L) → GL ((I × I) × I) L :=
    fun σ => (x₂ σ).kronecker (ρ.innerMatrix σ)
  have ha₃ := tensorSplittingChart_act_eq_kronecker e₂ e
    x₂ ρ.innerMatrix ha₂ ρ.act_eq_innerMatrix
  apply splittingChartIndex_prescribedDefect_isCoboundary_of_split
    (tensorSplittingChart e₂ e) f x₃ _ ha₃
  intro σ τ
  have h := SemilinearGaloisAction.kronecker_lifts_mul
    x₂ ρ.innerMatrix c₂ ρ.scalarDefect h₂ ρ.innerMatrix_mul σ τ
  simpa only [x₃, c₂, pow_succ, pow_zero, one_mul] using h

end Langlands.CentralSimple
