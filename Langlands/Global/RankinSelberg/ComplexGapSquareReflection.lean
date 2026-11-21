import Langlands.Global.RankinSelberg.ComplexGapSquareAverage
import Langlands.Global.RankinSelberg.ComplexAdjacentSplitEquation
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerGrowth
import Langlands.Global.RankinSelberg.ComplexGapLeadingCompact
import Langlands.Global.RankinSelberg.ComplexGapDualArguments
import Langlands.Representation.GodementJacquet.ComplexPrincipalSeriesMatrixEquation

/-! # Leading square reflection for a fixed Whittaker translate -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSquareReflection

open Langlands.Archimedean (unitaryCompact complexStandardModule)
open Langlands.Archimedean.ComplexReverseTwist (conjK continuous_conjK conjK_val conjAut)
open Langlands.GeneralLinear (determinant inverseTranspose continuous_inverseTranspose)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData HasStripExponentialGrowth)
open Langlands.Automorphic (complexStandardKFinite)
open ComplexAdjacentUnfolding (twistedSquare_normalization splitSquareTransform
  splitSquareTransform_eq_matrixTransform_neg exists_inducedUnitaryMeasure)
open ComplexGapSquareAverage (squareKernel squareKernel_average whittakerLeftTranslate_bound)
open ComplexJacquet (HasComplexPairNormalizedGrowth complexAdjacentCompactWeight complexLocalCompactProjectionReduction)
open ComplexLocalWhittakerGrowth (complexWhittakerCompactProjection)
open ComplexSquareFourier (matrixTransform)
open ComplexSquareZeta (compactCoefficient)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable (t : ℕ)
local notation "k" => t + 1
local notation "H" => Langlands.GeneralLinear (t + 1) ℂ
local notation "K" => unitaryCompact ℂ (t + 1)
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ
local notation "ι" => inverseTranspose (t + 1) ℂ

open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz operatorToEntry)
open ComplexGapLeadingFourier (leadingRestriction stackRows stackRows_left stackRows_right)
open ComplexGapDualArguments (leading)
open ComplexGodementFourier (rectFourier)

variable {t} in
private def entryToSquare (Φ : EntrySchwartz k k) : 𝓢(M, ℂ) :=
  @SchwartzMap.compCLMOfContinuousLinearEquiv ℂ M M ℂ
    Matrix.normedAddCommGroup Matrix.normedSpace _ _ _
    Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace _
    (ContinuousLinearEquiv.refl ℝ M) Φ

/-- The leading square restriction, presented with the matrix norm of the square zeta theorem. -/
def leadingSquareTest (q : ℕ) (C : Langlands.GeneralLinear (k + q + 1) ℂ)
    (Φ : EntrySchwartz (k + q + 1) k) : 𝓢(M, ℂ) :=
  entryToSquare (leadingRestriction k (q + 1) k C Φ)

theorem leadingSquareTest_apply (q : ℕ) (C : Langlands.GeneralLinear (k + q + 1) ℂ)
    (Φ : EntrySchwartz (k + q + 1) k) (X : M) :
    leadingSquareTest t q C Φ X = Φ (C.val * stackRows k (q + 1) k X 0) := rfl

/-- At a group argument the leading square test reads the first columns of the whole matrix. -/
theorem leadingSquareTest_group (q : ℕ) (C : Langlands.GeneralLinear (k + q + 1) ℂ)
    (Φ : EntrySchwartz (k + q + 1) k) (h : H) :
    leadingSquareTest t q C Φ h.val = Φ (leading k q (C * Langlands.GeneralLinear.rankInclusion (q + 1) h)) := by
  let A := Langlands.GeneralLinear.rankInclusion (R := ℂ) (n := k) (q + 1)
  have hA : leading k q (A h) = stackRows k (q + 1) k h.val 0 := by
    funext i j
    refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
    · exact (Langlands.GeneralLinear.blockSum_apply_left h 1 i₀ j).trans
        (congrFun (stackRows_left k (q + 1) k h.val 0 i₀) j).symm
    · exact (Langlands.GeneralLinear.blockSum_apply_right_left h 1 i₁ j).trans
        (congrFun (stackRows_right k (q + 1) k h.val 0 i₁) j).symm
  rw [leadingSquareTest_apply]
  change Φ (C.val * stackRows k (q + 1) k h.val 0) = Φ (C.val * leading k q (A h))
  rw [hA]

/-- The positive transform in the matched rectangle fiber is the positive square transform. -/
theorem leadingSquareTest_fourier (q : ℕ) (a : ℂˣ) (C : Langlands.GeneralLinear (k + q + 1) ℂ)
    (Φ : EntrySchwartz (k + q + 1) k) (X : M) :
    splitSquareTransform a (leadingSquareTest t q C Φ) X =
      rectFourier a (leadingRestriction k (q + 1) k C Φ) X := by
  rw [splitSquareTransform_eq_matrixTransform_neg, ComplexSquareFourier.matrixTransform_apply,
    Langlands.GodementJacquet.complexSelfDualMeasure_neg_scale]
  unfold rectFourier
  apply integral_congr_ae
  refine ae_of_all _ fun Y => ?_
  let Y' : M := Y
  have ht : Matrix.trace (X.transpose * Y') = ∑ i, ∑ j, Y' i j * X i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  change (leadingRestriction k (q + 1) k C Φ) Y' *
      ComplexGodementFourier.psi (-a) (-(Matrix.trace (X.transpose * Y'))) =
    (leadingRestriction k (q + 1) k C Φ) Y' * ComplexGodementFourier.psi a (∑ i, ∑ j, Y' i j * X i j)
  rw [ht]
  simp only [ComplexGodementFourier.psi, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    Langlands.LocalFactor.Archimedean.complexScaledCharacter_apply, Units.val_neg, neg_mul, mul_neg, neg_neg]

theorem leadingSquareTest_finite (q : ℕ) (p : ComplexGapTriangularChart.Outer k q)
    (Z : Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ)
    (P : MvPolynomial (ComplexGodementGaussianPolynomial.Coordinates (k + q + 1) k) ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : K => fun X : M =>
      leadingSquareTest t q (ComplexGapDualChart.retainedTail k q p Z)
        (operatorToEntry (ComplexGodementGaussianPolynomial.gaussianPolynomial P)) (u.val⁻¹.val * X))) :=
  ComplexGapLeadingCompact.complexGapLeadingCompact k q p Z P

variable {t} in
private theorem squareKernel_sum_integral (ν : Measure H) (d : ComplexCharacterData)
    (Φ : M → ℂ) (s : ℂ) (f : H → ℂ) (m : ℕ) (c : Fin m → ℂ) (C : Fin m → H → ℂ)
    (hf : ∀ y, f y = ∑ j, c j * C j y)
    (hC : ∀ j, Integrable (squareKernel d Φ (C j) s) ν) :
    (∫ y, squareKernel d Φ f s y ∂ν) = ∑ j, c j * ∫ y, squareKernel d Φ (C j) s y ∂ν := by
  have h (y : H) : squareKernel d Φ f s y = ∑ j, c j * squareKernel d Φ (C j) s y := by
    rw [squareKernel, hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold squareKernel
    ring
  simp_rw [h]
  rw [integral_finsetSum Finset.univ (fun j _ => (hC j).const_mul _)]
  simp only [integral_const_mul]

/-- The square pair of the retained rank at a fixed Whittaker evaluation point has the
adjoining-character normalization, with exponential growth on vertical strips. -/
def ComplexGapSquareReflectionStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData) (es : List ComplexCharacterData), es.length = k →
  ∀ (Φ : 𝓢(M, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : K => fun X => Φ (u.val⁻¹.val * X))) →
  ∀ (B : complexStandardKFinite k es →ₗ[ℂ] (H → ℂ)), IsComplexWhittakerIntertwiner t es a B →
  ∀ (f : complexStandardKFinite k es) (x : H),
    let Z := squareKernel d Φ (fun y => B f (x * y))
    let Zd := squareKernel d.inv (splitSquareTransform a Φ) (fun y => B f (x * ι y))
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (Z s) ν ∧ Integrable (Zd s) ν) ∧
    HasComplexPairNormalizedGrowth [d] es a 1 (fun s => ∫ y, Z s y ∂ν) (fun s => ∫ y, Zd s y ∂ν)

set_option maxHeartbeats 1400000 in
/-- Compact projection separates the leading coefficient into finitely many standard coefficients. -/
theorem complexGapSquareReflection : ComplexGapSquareReflectionStatement t := by
  intro ν _ κ _ hκ a d es hes Φ hΦ B hB f x
  dsimp only
  let F (y : H) := B f (x * y)
  let Fd (y : H) := F (ι y)
  let Φd := splitSquareTransform a Φ
  have hv : B f ∈ complexWhittakerModel t es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hF : Continuous F := (contMDiff_of_mem_complexWhittakerModel hv).continuous.comp
    (continuous_const.mul continuous_id)
  have hFd : Continuous Fd := hF.comp (continuous_inverseTranspose _ _)
  obtain ⟨CF, NF, hCF, hb⟩ := whittakerLeftTranslate_bound hv x
  have hbD (g : H) : ‖Fd g‖ ≤ CF * complexMatrixHeight g ^ NF := by
    simpa only [Fd, Langlands.GodementJacquet.complexMatrixHeight_inverseTranspose] using hb (ι g)
  obtain ⟨w, hw, hwfin, hRec, hRecD⟩ := complexAdjacentCompactWeight κ d.character.toMonoidHom
    d.character.continuous (-a) Φ hΦ
  obtain ⟨κ', hκ'fin, hκ', hκeq⟩ := exists_inducedUnitaryMeasure κ
  have hmean (X : M) : (∫ u, w u * (d.character ((determinant (id u : K).val)⁻¹) : ℂ) *
      Φ ((id u : K).val⁻¹.val * X) ∂κ') = Φ X := by
    rw [← hκeq, ← hRec X]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    exact mul_assoc _ _ _
  have hmeanD (X : M) : (∫ u, w u * (d.inv.character ((determinant (conjK k u).val)⁻¹) : ℂ) *
      Φd ((conjK k u).val⁻¹.val * X) ∂κ') = Φd X := by
    dsimp only [Φd]
    rw [splitSquareTransform_eq_matrixTransform_neg, ← hκeq, ← hRecD X]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    let g := (conjK k u).val
    have hχ : (d.inv.character ((determinant g)⁻¹) : ℂ) = (d.character (determinant g) : ℂ) := by
      rw [ComplexCharacterData.inv_character_apply, map_inv, Units.val_inv_eq_inv_val, inv_inv]
    change w u * (d.inv.character ((determinant g)⁻¹) : ℂ) * matrixTransform (-a) Φ (g⁻¹.val * X) =
      w u * ((d.character (determinant g) : ℂ) * matrixTransform (-a) Φ (g⁻¹.val * X))
    rw [hχ, mul_assoc]
  obtain ⟨sA, hA⟩ := @squareKernel_average t ν _ κ' hκ'fin id continuous_id w hw d Φ F hF
    ⟨CF, NF, hCF, hb⟩ hmean
  obtain ⟨sD, hD⟩ := @squareKernel_average t ν _ κ' hκ'fin (conjK k) continuous_conjK w hw d.inv Φd Fd hFd
    ⟨CF, NF, hCF, hbD⟩ hmeanD
  choose p hp using fun y => complexWhittakerCompactProjection (r := t) es a κ hκ ⟨w, hw⟩ hwfin B hB f y
  obtain ⟨m, Q, w', hQ, hExp⟩ := complexLocalCompactProjectionReduction (r := t) es a κ hκ w hw hwfin f B hB
    p (fun y (u : K) => (hp y).1 u.val) (fun y z => (hp z).2 y)
  let C (j : Fin m) := compactCoefficient κ' id (w' j) f.val
  have hC (j : Fin m) (z : H) : (∫ u, w' j u * f.val (u.val * z) ∂κ) = C j z :=
    hκeq _
  have hAvg (y : H) : compactCoefficient κ' id w F y = ∑ j, Q j x * C j y := by
    change (∫ u, w u * B f (x * (u.val * y)) ∂κ') = _
    rw [← hκeq]
    simpa only [mul_assoc, hC] using (hExp x y).1
  have hAvgD (y : H) : compactCoefficient κ' (conjK k) w Fd y = ∑ j, Q j x * C j (ι y) := by
    rw [← hAvg]
    unfold compactCoefficient
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    have hI : ι ((conjK k u).val) = u.val := by
      change ι (ι u.val) = u.val
      exact Langlands.GeneralLinear.inverseTranspose_involutive _ _ _
    simp only [Fd, F, map_mul, hI, id_eq]
  let es' (i : Fin k) := es.get (i.cast hes.symm)
  have he : List.ofFn es' = es := (List.ofFn_congr hes es.get).symm.trans (List.ofFn_get es)
  have hf : f.val ∈ complexStandardModule k (List.ofFn es') := he.symm ▸ f.2.1
  have hZ (j : Fin m) := twistedSquare_normalization ν κ' hκ'fin hκ' a d es' Φ f.val hf (w' j) (hQ j).2
  choose sZ hZi using fun j => (hZ j).1
  obtain ⟨σ, hσ⟩ := (Set.finite_range sZ).bddAbove
  let Z (j : Fin m) := squareKernel d Φ (C j)
  let Zd (j : Fin m) := squareKernel d.inv Φd (fun y => C j (ι y))
  have hn (j : Fin m) : HasComplexPairNormalizedGrowth [d] es a 1
      (fun s => ∫ y, Z j s y ∂ν) (fun s => ∫ y, Zd j s y ∂ν) := by
    simpa only [Z, Zd, squareKernel, he, C, Φd] using (hZ j).2
  choose N Nd hN using hn
  choose sN hR using fun j => (hN j).2.2.2.2.1
  obtain ⟨τ, hτ⟩ := (Set.finite_range sN).bddAbove
  let b := max (max sA sD) (max σ τ)
  have hDom (s : ℂ) (hs : b < s.re) (j : Fin m) : Integrable (Z j s) ν ∧ Integrable (Zd j s) ν :=
    hZi j s ((hσ (Set.mem_range_self j)).trans_lt ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs)))
  have hIA (s : ℂ) (hs : b < s.re) := hA s ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hs))
  have hID (s : ℂ) (hs : b < s.re) := hD s ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hs))
  refine ⟨⟨b, fun s hs => ⟨(hIA s hs).1, (hID s hs).1⟩⟩,
    (fun s => ∑ j, Q j x * N j s), (fun s => ∑ j, Q j x * Nd j s), ?_, ?_, ?_, ?_, ⟨b, ?_⟩, ?_⟩
  · exact Differentiable.fun_sum fun j _ =>
      (differentiable_const (Q j x) : Differentiable ℂ (fun _ : ℂ => Q j x)).mul (hN j).1
  · exact Differentiable.fun_sum fun j _ =>
      (differentiable_const (Q j x) : Differentiable ℂ (fun _ : ℂ => Q j x)).mul (hN j).2.1
  · exact HasStripExponentialGrowth.fun_sum Finset.univ _ fun j _ => (hN j).2.2.1.const_mul _
  · exact HasStripExponentialGrowth.fun_sum Finset.univ _ fun j _ => (hN j).2.2.2.1.const_mul _
  · intro s hs
    have hRj (j : Fin m) := hR j s ((hτ (Set.mem_range_self j)).trans_lt
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs)))
    constructor
    · change (∑ j, Q j x * N j s) = _ * ∫ y, squareKernel d Φ F s y ∂ν
      rw [(hIA s hs).2, squareKernel_sum_integral ν d Φ s _ m (fun j => Q j x) C hAvg
        (fun j => (hDom s hs j).1), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hRj j).1]
      ring
    · change (∑ j, Q j x * Nd j s) = _ * ∫ y, squareKernel d.inv Φd Fd s y ∂ν
      rw [(hID s hs).2, squareKernel_sum_integral ν d.inv Φd s _ m (fun j => Q j x) (fun j y => C j (ι y)) hAvgD
        (fun j => (hDom s hs j).2), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hRj j).2]
      ring
  · intro s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hN j).2.2.2.2.2 s]
    ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapSquareReflection
