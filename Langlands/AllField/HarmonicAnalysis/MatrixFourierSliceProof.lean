import Langlands.HarmonicAnalysis.MatrixFourierSliceProof
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.HarmonicAnalysis.MatrixFourierSliceStatement
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
/-!
# Proof of the rectangular Fourier slice

For a p-adic field, every last-row cutoff `Φ` is realized by a rectangular
Schwartz–Bruhat function `Ψ` through the twisted integral
`∫ ψ(-x_{B,1}) Ψ(g⁻¹ x) dx = |det g|^A Φ(lastRow g)`, conditional on row
Fourier surjectivity in dimension `B`. The function `Ψ` is a product over
columns: a row Fourier kernel in the first column and the characteristic
function of integral rows in the others.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe u

section Columns




end Columns

/-- The rectangular Fourier slice, conditional on row Fourier surjectivity in
the row dimension. -/
theorem padicMatrixFourierSlice : PadicMatrixFourierSliceStatement.{u} := by
  intro F _ T a b hsurj
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ ν Φ
  -- The characteristic function of integral rows and its nonzero integral.
  let O : Set F := (T.Integers : Set F)
  have hOopen : IsOpen O := T.isOpen_integers
  have hOcompact : IsCompact O := T.isCompact_integers
  let S : Set (Fin (b + 1) → F) := Set.univ.pi fun _ => O
  have hSclopen : IsClopen S :=
    ⟨isClosed_set_pi fun _ _ => hOcompact.isClosed,
      isOpen_set_pi Set.finite_univ fun _ _ => hOopen⟩
  have hScompact : IsCompact S := isCompact_univ_pi fun _ => hOcompact
  let κ₀ : SchwartzBruhat (Fin (b + 1) → F) :=
    Hecke.TestFunction.characteristic hSclopen hScompact
  let I₀ : ℂ := ∫ v, κ₀ v ∂rowMeasure ν (b + 1)
  have hI₀ : I₀ ≠ 0 := by
    have hval : I₀ = ((rowMeasure ν (b + 1)).real S : ℂ) := by
      change ∫ v, S.indicator (fun _ => (1 : ℂ)) v ∂rowMeasure ν (b + 1) = _
      rw [integral_indicator_const _ hSclopen.isOpen.measurableSet]
      simp
    rw [hval, Complex.ofReal_ne_zero, Measure.real, ENNReal.toReal_ne_zero]
    refine ⟨?_, hScompact.measure_lt_top.ne⟩
    exact (hSclopen.isOpen.measure_pos _ ⟨0, fun i _ => (T.Integers).zero_mem⟩).ne'
  -- The constant relating the matrix measure to the product of row measures.
  obtain ⟨c, hc, hcol⟩ := exists_columnProduct_integral
    (RankinSelberg.rectangularMeasure ν (b + 1) (a + 1)) ν
  let C : ℂ := (c : ℂ) * I₀ ^ a
  have hC : C ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hc.ne'))
      (pow_ne_zero a hI₀)
  -- The row kernel in the first column.
  let Φ' : SchwartzBruhat (Fin (b + 1) → F) :=
    C⁻¹ • Hecke.TestFunction.pullback (Homeomorph.neg (Fin (b + 1) → F)) Φ
  obtain ⟨κ, hκ⟩ := hsurj ψ ν Φ'
  let h : Fin (a + 1) → SchwartzBruhat (Fin (b + 1) → F) :=
    Fin.cons κ fun _ => κ₀
  refine ⟨columnProduct h, fun g => ?_⟩
  let μ := RankinSelberg.rectangularMeasure ν (b + 1) (a + 1)
  let l := RankinSelberg.lastRow g
  -- The integrand after the substitution `x = g y`.
  let G : Matrix (Fin (b + 1)) (Fin (a + 1)) F → ℂ := fun y =>
    ψ.complex (-((g.val * y) (Fin.last b) 0)) * columnProduct h y
  have hG : Continuous G :=
    (ψ.continuous_complex.comp
      ((continuous_const.matrix_mul continuous_id).matrix_elem _ _).neg).mul
      (columnProduct h).continuous
  have hmul : Continuous fun x : Matrix (Fin (b + 1)) (Fin (a + 1)) F =>
      (g⁻¹ : GeneralLinear (b + 1) F).val * x :=
    continuous_const.matrix_mul continuous_id
  have hscale := padicRectangularHaarScaling F T (b + 1) (a + 1) μ g⁻¹ 1
  simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, one_pow, div_one, map_inv,
    Units.val_inv_eq_inv_val, inv_pow, inv_inv] at hscale
  have hsubst : ∀ x : Matrix (Fin (b + 1)) (Fin (a + 1)) F,
      ψ.complex (-(x (Fin.last b) 0)) *
          columnProduct h ((g⁻¹ : GeneralLinear (b + 1) F).val * x) =
        G ((g⁻¹ : GeneralLinear (b + 1) F).val * x) := by
    intro x
    simp only [G, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  -- The integrand as a column product.
  let f : Fin (a + 1) → (Fin (b + 1) → F) → ℂ :=
    Fin.cons (fun v => ψ.complex (rowPairing v (-l)) * κ v) fun _ v => κ₀ v
  have hGf : G = fun y => ∏ j, f j (fun i => y i j) := by
    funext y
    have hpair : -((g.val * y) (Fin.last b) 0) = rowPairing (fun i => y i 0) (-l) := by
      simp [rowPairing, Matrix.mul_apply, l, RankinSelberg.lastRow, mul_comm]
    simp only [G, columnProduct_apply, Fin.prod_univ_succ, f, h, Fin.cons_zero,
      Fin.cons_succ, hpair, mul_assoc]
  have hint : ∫ y, G y ∂μ =
      (c : ℂ) * (rowFourierIntegral ψ ν (b + 1) κ (-l) * I₀ ^ a) := by
    rw [hGf, hcol f, Fin.prod_univ_succ]
    simp only [f, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rfl
  have hΦ' : Φ' (-l) = C⁻¹ * Φ l := by
    change C⁻¹ * Φ (-(-l)) = _
    rw [neg_neg]
  have hkey : (c : ℂ) * (C⁻¹ * Φ l * I₀ ^ a) = Φ l := by
    rw [show (c : ℂ) * (C⁻¹ * Φ l * I₀ ^ a) = C⁻¹ * C * Φ l by simp only [C]; ring,
      inv_mul_cancel₀ hC, one_mul]
  calc ∫ x, ψ.complex (-(x (Fin.last b) 0)) *
          columnProduct h ((g⁻¹ : GeneralLinear (b + 1) F).val * x) ∂μ
      = ∫ x, G ((g⁻¹ : GeneralLinear (b + 1) F).val * x) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hsubst)
    _ = ∫ y, G y ∂(μ.map fun x => (g⁻¹ : GeneralLinear (b + 1) F).val * x) :=
        (integral_map hmul.aemeasurable hG.aestronglyMeasurable).symm
    _ = ((T.determinantNorm (b + 1) g : ℝ≥0) ^ (a + 1) : ℝ≥0) • ∫ y, G y ∂μ := by
        rw [hscale, integral_smul_nnreal_measure]
    _ = (T.normalizedAbs (Matrix.det g.val) : ℂ) ^ (a + 1) * Φ (RankinSelberg.lastRow g) := by
        rw [hint, ← hκ (-l), hΦ', hkey, NNReal.smul_def, Complex.real_smul, NNReal.coe_pow,
          Complex.ofReal_pow, T.determinantNorm_coe]
        rfl

end Langlands.AllField.HarmonicAnalysis
