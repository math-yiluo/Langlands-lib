import Langlands.Global.RankinSelberg.ComplexGapSplitGaussian
import Langlands.Global.RankinSelberg.ComplexGapWeylConvergence

/-! # The alternate Weyl integral for Gaussian monomials -/

noncomputable section

open MeasureTheory MvPolynomial
open scoped Matrix Matrix.Norms.Elementwise SchwartzMap NNReal ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapWeylGaussianUnfolding

open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (determinant)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure complexUnequalIntegral)
open ComplexGapSplitPartialRestriction (HasSplitPartialTest)
open ComplexGapRightChart (tailSize)
open ComplexGapSplitGaussian (complexGapSplitGaussian splitGaussianMonomial splitGaussianMonomial_schwartz)
open ComplexGapTailExchange (SplitTailTest)
open ComplexGapTriangularChart (outerMeasure)
open ComplexGapWeylConvergence (HasSchwartzTailFactors complexGapWeylConvergence)
open ComplexGapWeylTranslation (complexGapWeylTranslation weylCoordinate)
open ComplexGapWeylUnfolding (weylUnfoldedKernel complexGapWeylUnfolding)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue rightTest)
open ComplexGodementColumnProduct (schwartzProd schwartzProd_apply)
open ComplexGodementFourier (fourier exists_schwartz_fourier)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial)
open ComplexJacquetUnipotentMeasure (entryHaar)

local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

private def emptyColumnProduct (m : ℕ) : 𝓢(Mat m 0, ℂ) := by
  have hC : IsCompact (Set.univ : Set (Mat m 0)) := by
    have h : (Set.univ : Set (Mat m 0)) = {0} := by
      ext x
      exact iff_of_true trivial (Subsingleton.elim x 0)
    rw [h]
    exact isCompact_singleton
  have h : HasCompactSupport (fun _ : Mat m 0 => (1 : ℂ)) :=
    hC.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  exact h.toSchwartzMap contDiff_const

private def leadingColumnsCLM (m n : ℕ) : Mat m (n + 1) →L[ℝ] Mat m n :=
  ({ toFun A := fun i j => A i j.castSucc
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : Mat m (n + 1) →ₗ[ℝ] Mat m n).toContinuousLinearMap

private def lastColumnCLM (m n : ℕ) : Mat m (n + 1) →L[ℝ] (Fin m → ℂ) :=
  ({ toFun A := fun i => A i (Fin.last n)
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : Mat m (n + 1) →ₗ[ℝ] (Fin m → ℂ)).toContinuousLinearMap

private theorem norm_le_columnPair (m n : ℕ) (A : Mat m (n + 1)) :
    ‖A‖ ≤ 1 * (‖leadingColumnsCLM m n A‖ + ‖lastColumnCLM m n A‖) := by
  rw [one_mul]
  refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_
  refine Fin.lastCases ?_ (fun j₀ => ?_) j
  · have h := norm_le_pi_norm (lastColumnCLM m n A) i
    exact h.trans (le_add_of_nonneg_left (norm_nonneg _))
  · have h := Matrix.norm_entry_le_entrywise_sup_norm (leadingColumnsCLM m n A) (i := i) (j := j₀)
    exact h.trans (le_add_of_nonneg_right (norm_nonneg _))

private def columnProductSchwartz (m : ℕ) :
    (n : ℕ) → (Fin n → 𝓢(Fin m → ℂ, ℂ)) → 𝓢(Mat m n, ℂ)
  | 0, _ => emptyColumnProduct m
  | n + 1, f =>
    schwartzProd (leadingColumnsCLM m n) (lastColumnCLM m n)
      zero_le_one (norm_le_columnPair m n)
      (columnProductSchwartz m n (f ∘ Fin.castSucc)) (f (Fin.last n))

private theorem columnProductSchwartz_apply (m n : ℕ) (f : Fin n → 𝓢(Fin m → ℂ, ℂ)) (A : Mat m n) :
    columnProductSchwartz m n f A = ∏ j : Fin n, f j (fun i => A i j) := by
  induction n with
  | zero =>
      rw [Fin.prod_univ_zero]
      rfl
  | succ n ih =>
      rw [columnProductSchwartz, schwartzProd_apply, ih, Fin.prod_univ_castSucc]
      rfl

variable (t q : ℕ)

local notation "Small" => (t + 1)
local notation "Order" => (t + 1 + q)
local notation "Size" => (t + 1 + q + 1)
local notation "Δ" => (t + 1 + q + 1 - (t + 1))
local notation "e" => (tailSize Small q)
local notation "Row" => (Fin Size → ℂ)
local notation "Rect" => Mat Size (Size + 1)
local notation "Compact" => unitaryCompact ℂ Size
local notation "Exponents" => (Coordinates Size (Size + 1) →₀ ℕ)

private theorem splitGaussian_hasSchwartzTailFactors (a : ℂˣ) (b : Exponents) (c : ℂ) :
    let T := splitGaussianMonomial Small q a b c
    ∃ (Φ : 𝓢(Mat Size Small, ℂ)) (φ : 𝓢(Row, ℂ)) (Ξ : 𝓢(Mat Size Δ, ℂ)),
      HasSchwartzTailFactors t q a T Φ φ Ξ := by
  intro T
  obtain ⟨Φ, φ, ψ, hΦ, hφ, hψ⟩ := splitGaussianMonomial_schwartz Small q a b c
  have hF (j : Fin q) := exists_schwartz_fourier a (T.later j)
  choose Ψ hΨ using hF
  let R := (Matrix.reindexLinearEquiv ℝ ℂ (Equiv.refl (Fin Size)) (finCongr (e).symm)).toContinuousLinearEquiv
  let f : Fin (q + 1) → 𝓢(Row, ℂ) := Fin.lastCases ψ Ψ
  let Ξ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ R (columnProductSchwartz Size (q + 1) f)
  refine ⟨Φ, φ, Ξ, hΦ, hφ, ?_⟩
  intro A
  rw [show T.lastFrequency = ψ from hψ]
  change _ = columnProductSchwartz Size (q + 1) f (R A)
  rw [columnProductSchwartz_apply, Fin.prod_univ_castSucc]
  simp only [f, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hR (j : Fin (q + 1)) : (fun i => R A i j) = fun i => A i (finCongr e j) := rfl
  simp_rw [hR]
  simp_rw [hΨ]
  exact mul_comm _ _

private theorem gap_lt : t < Order + 1 := by omega

/-- The actual ordinary integral of each Weyl-translated continued Gaussian monomial
has the alternate quotient expression in its domain of absolute convergence. -/
def ComplexGapWeylGaussianUnfoldingStatement : Prop :=
  ∀ (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel Order ds (-a)) (V : complexWhittakerModel t es a)
    (D : ComplexQuotientMeasureData t) (κ : Measure Compact), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ (cHaar : ℝ≥0) (σ τ : ℝ), 0 < cHaar ∧
    ∀ (d : ComplexCharacterData) (b : Exponents) (c z s : ℂ),
      let w := ArchimedeanLocal.unfoldingWeyl (K := ℂ) (gap_lt t q)
      let u := s - ((q + 1 : ℕ) : ℂ) / 2
      let ζ := (((Order + 2 : ℕ) : ℂ) / 2 + z - 1)
      σ ≤ u.re → τ ≤ (d.exponent + ζ + u).re →
      let μ := complexSelfDualMeasure a
      let ν := complexGeneralLinearHaar Size
      let Φ := operatorToEntry (gaussianPolynomial (monomial b c))
      let T := splitGaussianMonomial Small q a (b.mapDomain (weylCoordinate (gap_lt t q))) c
      let η := (outerMeasure Small q μ κ).prod (entryHaar μ (q + 1))
      let F := weylUnfoldedKernel t q a T (characterWeight d ζ) W.val V.val u
      Integrable F (η.prod D.measure) ∧
      complexUnequalIntegral (gap_lt t q) D
        (fun g => continuedValue ν μ d a Φ W.val (g * w) z) V.val s =
        ((d.character (determinant w) : ℂ) * (d.character ((-1 : ℂˣ) ^ Size) : ℂ)) *
          (cHaar : ℂ) * ∫ p, ∫ x, F (p, x) ∂D.measure ∂η

set_option maxHeartbeats 950000 in
theorem complexGapWeylGaussianUnfolding : ComplexGapWeylGaussianUnfoldingStatement t q := by
  intro a ds es W V D κ hκ hκinv
  obtain ⟨cHaar, hcHaar, hUnfold⟩ := complexGapWeylUnfolding t q a κ hκ hκinv
  obtain ⟨σ, τ, hConv⟩ := complexGapWeylConvergence t q a ds es W V D κ hκ
  refine ⟨cHaar, σ, τ, hcHaar, ?_⟩
  intro d b c z s w u ζ hσ hτ μ ν Φ T η F
  let b' := b.mapDomain (weylCoordinate (gap_lt t q))
  have hWeyl : rightTest w Φ = operatorToEntry (gaussianPolynomial (monomial b' c)) :=
    complexGapWeylTranslation (r := Order) (t := t) (gap_lt t q) b c
  have hSplit : HasSplitPartialTest Small q a (rightTest w Φ) T := by
    rw [hWeyl]
    exact complexGapSplitGaussian Small q a b' c
  obtain ⟨L, P, Ξ, hFactors⟩ := splitGaussian_hasSchwartzTailFactors t q a b' c
  have hF := hConv d ζ u hσ hτ T L P Ξ hFactors
  exact ⟨hF, hUnfold D d ds es Φ T hSplit W V z s hF⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGapWeylGaussianUnfolding
