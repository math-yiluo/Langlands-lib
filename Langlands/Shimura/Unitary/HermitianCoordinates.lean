import Langlands.Shimura.Unitary.FiniteMatrixChart
import Langlands.Shimura.Unitary.HermitianAdjointChart
import Langlands.Shimura.Unitary.NonsplitCompletionChart
import Langlands.Shimura.Unitary.RealMatrixChart

/-! # Hermitian coordinates on the actual completed CM algebra -/

noncomputable section

universe u v w

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped TensorProduct FiniteExtension

/-- Matrix coordinates with their specified center inclusion and Hermitian Gram matrix. -/
structure HermitianMatrixChart {R C B : Type*} [CommRing R] [Field C] [Ring B]
    [Algebra R C] [Algebra R B] (ι : C →ₐ[R] B) (c : AlgebraInvolution R C)
    (σ : AlgebraInvolution R B) (n : ℕ) where
  equiv : B ≃ₐ[R] Matrix (Fin n) (Fin n) C
  center_eq (z : C) : equiv (ι z) = Matrix.scalar (Fin n) z
  gram : (Matrix (Fin n) (Fin n) C)ˣ
  hermitian : matrixTranspose c n (gram : Matrix (Fin n) (Fin n) C) = gram
  adjoint_eq (b : B) : equiv (σ b) = (matrixTranspose c n).adjoint gram hermitian (equiv b)

/-- A center-compatible matrix equivalence in positive size has a Hermitian Gram
matrix for an involution whose action on the specified center is the given
nontrivial coefficient involution. -/
def HermitianMatrixChart.ofEquiv {R C B : Type*} [CommRing R] [Field C] [Ring B]
    [Algebra R C] [Algebra R B] {ι : C →ₐ[R] B} {c : AlgebraInvolution R C}
    {σ : AlgebraInvolution R B} {n : ℕ} (hn : 0 < n) (hc : ∃ z, c z ≠ z)
    (hσ : ∀ z, σ (ι z) = ι (c z)) (e : B ≃ₐ[R] Matrix (Fin n) (Fin n) C)
    (he : ∀ z, e (ι z) = Matrix.scalar (Fin n) z) : HermitianMatrixChart ι c σ n := by
  let ρ := σ.transport e
  have hρ (z : C) : ρ (algebraMap C (Matrix (Fin n) (Fin n) C) z) =
      algebraMap C (Matrix (Fin n) (Fin n) C) (c z) := by
    change ρ (Matrix.scalar (Fin n) z) = Matrix.scalar (Fin n) (c z)
    rw [← he, AlgebraInvolution.transport_equiv, hσ, he]
  let G := hermitianGramOfMatrixInvolution c hn hc ρ hρ
  exact ⟨e, he, G.val, G.property.choose, fun b =>
    (AlgebraInvolution.transport_equiv σ e b).symm.trans (G.property.choose_spec (e b))⟩

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]

/-- At a real embedding the involution is a Hermitian adjoint on the actual complex matrix chart. -/
def realHermitianChart {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n)
    (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    HermitianMatrixChart ((realCenterInclusion (A := A) τ).comp
      (realCenterEquiv (K := K) τ).symm.toAlgHom)
      (AlgebraInvolution.ofStar (R := ℝ) (A := ℂ)) (D.involution.baseChange ℝ) n := by
  let : Algebra E ℝ := τ.toAlgebra
  let C := realCenterEquiv (K := K) τ
  let M := realMatrixChart τ D
  apply HermitianMatrixChart.ofEquiv hn (e := M.val)
  · refine ⟨Complex.I, fun h => ?_⟩
    change star Complex.I = Complex.I at h
    have he := congrArg Complex.im h
    simp at he
    norm_num at he
  · intro z
    change D.involution.baseChange ℝ (realCenterInclusion τ (C.symm z)) =
      realCenterInclusion τ (C.symm (star z))
    rw [realInvolution_center]
    congr 1
    apply C.injective
    rw [C.apply_symm_apply, realCenterEquiv_conjugation]
    exact congrArg star (C.apply_symm_apply z)
  · intro z
    change M.val (realCenterInclusion τ (C.symm z)) = _
    rw [M.property, C.apply_symm_apply]

variable (p : Langlands.Global.FinitePlace E)

local notation "F" => FiniteCompletion E p
local notation "L" => FiniteCompletion K (Subtype.val (placeAbove K p))

/-- Completed conjugation at the unique upper completion of a nonsplit finite place. -/
def nonsplitCoefficientInvolution (hp : ¬ IsSplitPlace E K p) : AlgebraInvolution F L :=
  (localConjugation E K p).transport (nonsplitCompletionCenterEquiv p hp)

/-- The actual local algebra with zero upper invariant has Hermitian matrix
coordinates over the upper field at a nonsplit finite place. -/
def nonsplitHermitianChart {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n)
    (hp : ¬ IsSplitPlace E K p)
    (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0) :
    HermitianMatrixChart ((localCenterMap E K A p).comp
      (nonsplitCompletionCenterEquiv p hp).symm.toAlgHom) (nonsplitCoefficientInvolution p hp)
      (localInvolution D.toSecondKindInvolution p) n := by
  let C := nonsplitCompletionCenterEquiv p hp
  let M := finiteMatrixChartOfZeroInvariants p D hz
  apply HermitianMatrixChart.ofEquiv hn (e := M.val.trans C.mapMatrix)
  · obtain ⟨z, hz⟩ := exists_localConjugation_ne (K := K) p
    refine ⟨C z, fun h => hz (C.injective ?_)⟩
    change (localConjugation E K p).transport C (C z) = C z at h
    rwa [AlgebraInvolution.transport_equiv] at h
  · intro z
    change localInvolution D.toSecondKindInvolution p (localCenterMap E K A p (C.symm z)) =
      localCenterMap E K A p (C.symm (C (localConjugation E K p (C.symm z))))
    rw [C.symm_apply_apply, localInvolution_center]
  · intro z
    change C.mapMatrix (M.val (localCenterMap E K A p (C.symm z))) = _
    rw [M.property]
    apply Matrix.ext
    intro i j
    change C (Matrix.scalar (Fin n) (C.symm z) i j) = Matrix.scalar (Fin n) z i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

end Langlands.Shimura.FiniteUnitary
