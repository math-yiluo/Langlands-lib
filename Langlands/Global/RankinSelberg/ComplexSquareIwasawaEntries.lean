import Langlands.Global.RankinSelberg.ComplexGodementTriangularEntries
import Langlands.Global.RankinSelberg.ComplexLocalIwasawaHaar

/-! # Additive row entries in the left complex Iwasawa chart -/

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.GeneralLinear
open ComplexGodement (upperTriangularEntries)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squareIwasawaGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareIwasawaGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance squareIwasawaGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Y" => Fin n → ℝ
local notation "X" => UpperEntryPair n → ℂ

private def offEntryByRow (n : ℕ) : UpperEntryPair n ≃ (Σ i : Fin n, Fin (n - 1 - i.val)) where
  toFun p := ⟨p.1.1, ⟨p.1.2.val - p.1.1.val - 1, by
    have hp := p.2
    have hi := p.1.1.isLt
    have hj := p.1.2.isLt
    change p.1.1.val < p.1.2.val at hp
    change p.1.1.val < n at hi
    change p.1.2.val < n at hj
    omega⟩⟩
  invFun p := ⟨(p.1, ⟨p.1.val + 1 + p.2.val, by
    have hi := p.1.isLt
    have hj := p.2.isLt
    change p.1.val + 1 + p.2.val < n
    omega⟩), by
    change p.1.val < p.1.val + 1 + p.2.val
    omega⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl (Fin.ext ?_)
    have hp := p.2
    change p.1.1.val < p.1.2.val at hp
    change p.1.1.val + 1 + (p.1.2.val - p.1.1.val - 1) = p.1.2.val
    omega
  right_inv p := by
    rcases p with ⟨i, k⟩
    refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
    change i.val + 1 + k.val - i.val - 1 = k.val
    omega

private theorem prod_upperEntry_row {A : Type*} [CommMonoid A] (f : Fin n → A) :
    (∏ ij : UpperEntryPair n, f ij.1.1) = ∏ j : Fin n, f j ^ (n - 1 - j.val) := by
  calc
    _ = ∏ p : (Σ j : Fin n, Fin (n - 1 - j.val)), f p.1 :=
      Fintype.prod_equiv (offEntryByRow n) _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.prod_sigma]; simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The factor in each upper entry when the diagonal is multiplied on the left. -/
def scaleUpperRows (y : Y) (z : X) : X := fun ij => Real.exp (y ij.1.1) • z ij

theorem logTorus_mul_unipotent_val (y : Y) (u : N) :
    (logTorus y * u.val).val =
      upperTriangularEntries (fun i => (Real.exp (y i) : ℂ))
        (scaleUpperRows y (upperEntryCoordinates n u)) := by
  ext i j
  rw [Units.val_mul, logTorus_val, Matrix.diagonal_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [upperTriangularEntries, h, scaleUpperRows, upperEntryCoordinates_apply, Complex.real_smul]
  · simp [upperTriangularEntries, UpperUnipotent.entry_diag]
  · simp [upperTriangularEntries, not_lt_of_gt h, ne_of_gt h, u.2.1 h]

private def entryDensity (y : ℝ) : ℝ≥0 := ⟨(Real.exp y ^ 2)⁻¹, by positivity⟩

/-- The inverse Jacobian for strictly upper entries scaled by their row diagonal. -/
def upperRowJacobian (y : Y) : ℝ≥0 :=
  ∏ j : Fin n, entryDensity (y j) ^ (n - 1 - j.val)

theorem upperRowJacobian_coe (y : Y) :
    (upperRowJacobian y : ℝ) =
      ∏ j : Fin n, ((Real.exp (y j) ^ 2)⁻¹) ^ (n - 1 - j.val) := by
  simp only [upperRowJacobian, NNReal.coe_prod, NNReal.coe_pow]
  rfl

theorem upperRowJacobian_pos (y : Y) : 0 < upperRowJacobian y := by
  apply Finset.prod_pos
  intro j _
  apply pow_pos
  exact (show 0 < (entryDensity (y j) : ℝ) from inv_pos.mpr (pow_pos (Real.exp_pos _) 2))

theorem map_scaleUpperRows (y : Y) :
    (volume : Measure X).map (scaleUpperRows y) =
      upperRowJacobian y • (volume : Measure X) := by
  have hm (ij : UpperEntryPair n) : Measurable ((Real.exp (y ij.1.1)) • · : ℂ → ℂ) :=
    measurable_const_smul _
  have hs (ij : UpperEntryPair n) :
      (volume : Measure ℂ).map ((Real.exp (y ij.1.1)) • ·) =
        entryDensity (y ij.1.1) • (volume : Measure ℂ) := by
    rw [Measure.map_addHaar_smul volume (Real.exp_ne_zero _), Complex.finrank_real_complex,
      abs_of_pos (by positivity), ← Measure.coe_nnreal_smul, ← ENNReal.ofReal_coe_nnreal]
    rfl
  have hσ (ij : UpperEntryPair n) :
      SigmaFinite ((volume : Measure ℂ).map ((Real.exp (y ij.1.1)) • ·)) := by
    rw [hs]
    infer_instance
  change (Measure.pi (fun _ : UpperEntryPair n => (volume : Measure ℂ))).map
      (fun (z : X) ij => Real.exp (y ij.1.1) • z ij) =
    upperRowJacobian y • Measure.pi (fun _ : UpperEntryPair n => (volume : Measure ℂ))
  rw [Measure.pi_map_pi (hμ := hσ) (fun ij => (hm ij).aemeasurable)]
  simp_rw [hs]
  rw [Langlands.HarmonicAnalysis.pi_nnreal_smul]
  exact congrArg (fun c : ℝ≥0 => c • (volume : Measure X)) (prod_upperEntry_row fun j => entryDensity (y j))

private def scalarLebesgue : Langlands.HarmonicAnalysis.AdditiveHaarMeasure ℂ where
  measure := volume
  isAddHaar := inferInstance
  regular := inferInstance

local instance : SigmaFinite scalarLebesgue.measure :=
  inferInstanceAs (SigmaFinite (volume : Measure ℂ))

/-- The left Iwasawa Haar chart can use ordinary additive coordinates for the strictly upper
entries of the upper-unipotent factor. -/
def ComplexSquareIwasawaEntriesStatement : Prop :=
  ∀ (μ : Measure G) (κ : Measure K), μ.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • Measure.map
      (fun p : (Y × X) × K =>
        logTorus p.1.1 * ((upperEntryCoordinates n).symm p.1.2).val * p.2.val)
      (((volume : Measure Y).prod (volume : Measure X)).prod κ)

theorem complexSquareIwasawaEntries : ComplexSquareIwasawaEntriesStatement (n := n) := by
  intro μ κ hμ hκ
  let : κ.IsHaarMeasure := hκ
  let e : N ≃ₜ X := upperEntryCoordinates n
  let ν : Measure N := (volume : Measure X).map e.symm
  have hν : ν.IsHaarMeasure := upperEntryProductMeasure_isHaar (d := n) scalarLebesgue
  obtain ⟨c, hc, hEq⟩ := ComplexLocalIwasawaHaar.complexIwasawaHaar n μ ν κ hμ hν hκ
  let η := ((volume : Measure Y).prod (volume : Measure X)).prod κ
  let T : (Y × X) × K → (Y × N) × K := Prod.map (Prod.map id e.symm) id
  let q : (Y × N) × K → G := fun p => logTorus p.1.1 * p.1.2.val * p.2.val
  have hmT : Measurable T := (measurable_id.prodMap e.symm.measurable).prodMap measurable_id
  have hq : Measurable q :=
    ((ComplexLocalIwasawa.continuous_logTorus.measurable.comp (measurable_fst.comp measurable_fst)).mul
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))).mul
      (measurable_subtype_coe.comp measurable_snd)
  have hT : η.map T = ((volume : Measure Y).prod ν).prod κ := by
    change (((volume : Measure Y).prod (volume : Measure X)).prod κ).map
      (Prod.map (Prod.map id e.symm) id) = _
    rw [← Measure.map_prod_map _ _ (measurable_id.prodMap e.symm.measurable) measurable_id,
      ← Measure.map_prod_map _ _ measurable_id e.symm.measurable, Measure.map_id, Measure.map_id]
  refine ⟨c, hc, ?_⟩
  change μ = c • Measure.map q ((volume.prod ν).prod κ) at hEq
  rw [hEq, ← hT, Measure.map_map hq hmT]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
