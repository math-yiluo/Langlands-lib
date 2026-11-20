import Langlands.Representation.Archimedean.ComplexStandardModulus
import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Mathlib.MeasureTheory.Integral.Pi

/-! # Integrability on a chain of strict complex adjacent-swap charts -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct
open MeasureTheory Filter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

/-- A sequence of adjacent swaps that exchanges two characters in strictly
decreasing order of the real parts of their exponents at each step. -/
inductive StrictSwapChain (n : ℕ) : List ComplexCharacterData → List ComplexCharacterData → ℕ → Type
  | nil (ds : List ComplexCharacterData) : StrictSwapChain n ds ds 0
  | cons (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
      (hn : (pre ++ d :: e :: post).length = n) (i j : Fin n)
      (hi : (i : ℕ) = pre.length) (hj : (j : ℕ) = i + 1)
      (hre : 0 < (d.exponent - e.exponent).re)
      {fs : List ComplexCharacterData} {m : ℕ}
      (tail : StrictSwapChain n (pre ++ e :: d :: post) fs m) :
      StrictSwapChain n (pre ++ d :: e :: post) fs (m + 1)

namespace StrictSwapChain

variable {n m : ℕ} {ds es : List ComplexCharacterData}

/-- The product of the successive adjacent chart matrices, in the order in
which the swaps are applied. -/
def chartProduct : {ds es : List ComplexCharacterData} → {m : ℕ} →
    StrictSwapChain n ds es m → (Fin m → ℂ) → Langlands.GeneralLinear n ℂ
  | _, _, _, .nil _, _ => 1
  | _, _, _, .cons _ _ _ _ _ i j _ hj _ tail, z =>
      chart i j hj (z 0) * tail.chartProduct (fun l => z l.succ)

private theorem continuous_chart {i j : Fin n} (hj : (j : ℕ) = i + 1) :
    Continuous (chart i j hj) := by
  apply UpperBruhatCoordinates.continuous_generalLinear_of_val
  simp only [chart_val]
  exact continuous_const.mul (contDiff_transvection i j).continuous

theorem continuous_chartProduct (w : StrictSwapChain n ds es m) : Continuous w.chartProduct := by
  induction w with
  | nil => exact continuous_const
  | cons _ _ _ _ _ i j _ hj _ tail ih =>
    exact ((continuous_chart hj).comp (continuous_apply 0)).mul
      (ih.comp (continuous_pi fun l => continuous_apply l.succ))

private def splitCoordinates (m : ℕ) : (Fin (m + 1) → ℂ) ≃ᵐ ℂ × (Fin m → ℂ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0

private theorem measurePreserving_splitCoordinates (m : ℕ) :
    MeasurePreserving (splitCoordinates m) :=
  volume_preserving_piFinSuccAbove (fun _ => ℂ) 0

private theorem splitCoordinates_symm (z : ℂ × (Fin m → ℂ)) :
    (splitCoordinates m).symm z = Fin.cons z.1 z.2 := by
  rw [splitCoordinates, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero]
  simp only [cast_eq]

private theorem integrable_emptyCoordinates {E : Type*} [NormedAddCommGroup E] (c : E) :
    Integrable (fun _ : Fin 0 → ℂ => c) := by
  rw [integrable_const_iff]
  right
  constructor
  change Measure.pi (fun _ : Fin 0 => (volume : Measure ℂ)) Set.univ < ⊤
  rw [Measure.pi_empty_univ]
  exact ENNReal.one_lt_top

private theorem integral_emptyCoordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (c : E) : (∫ _ : Fin 0 → ℂ, c) = c := by
  rw [integral_const, measureReal_def]
  change (Measure.pi (fun _ : Fin 0 => (volume : Measure ℂ)) Set.univ).toReal • c = c
  rw [Measure.pi_empty_univ, ENNReal.toReal_one, one_smul]

set_option maxHeartbeats 800000 in
/-- The positive spherical majorant is integrable over the full product of the
swap charts. The integral is a positive scalar times the majorant for the final
list. -/
theorem integrable_modulusSpherical (w : StrictSwapChain n ds es m) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Langlands.GeneralLinear n ℂ,
      Integrable (fun z => ((modulusSpherical n ds).val (w.chartProduct z * g)).re) ∧
      (∫ z, ((modulusSpherical n ds).val (w.chartProduct z * g)).re) =
        C * ((modulusSpherical n es).val g).re := by
  induction w with
  | nil ds =>
    refine ⟨1, zero_lt_one, fun g => ?_⟩
    simp only [chartProduct, one_mul]
    exact ⟨integrable_emptyCoordinates _, integral_emptyCoordinates _⟩
  | @cons pre post d e hn i j hi hj hre fs m tail ih =>
    let ds := pre ++ d :: e :: post
    let es := pre ++ e :: d :: post
    obtain ⟨C, hC, hhead⟩ := integral_modulusSpherical_strictSwap pre post d e hn i j hi hj hre
    obtain ⟨D, hD, htail⟩ := ih
    refine ⟨C * D, mul_pos hC hD, fun g => ?_⟩
    let φ (z : ℂ × (Fin m → ℂ)) :=
      ((modulusSpherical n ds).val (chart i j hj z.1 * (tail.chartProduct z.2 * g))).re
    have hφ : Continuous φ :=
      Complex.continuous_re.comp ((mem_of_mem_kFs (modulusSpherical n ds).2).1.continuous.comp
        (((continuous_chart hj).comp continuous_fst).mul
          ((tail.continuous_chartProduct.comp continuous_snd).mul continuous_const)))
    have hφ_nonneg (z : ℂ × (Fin m → ℂ)) : 0 ≤ φ z := (modulusSpherical_pos ds _).le
    have hslice (x : Fin m → ℂ) :
        (∫ z, φ (z, x)) = C * ((modulusSpherical n es).val (tail.chartProduct x * g)).re :=
      hhead (tail.chartProduct x * g)
    have hφint : Integrable φ := by
      apply (integrable_prod_iff' hφ.aestronglyMeasurable).2
      refine ⟨Eventually.of_forall fun x => Integrable.of_integral_ne_zero
        ((hslice x).trans_ne (mul_pos hC (modulusSpherical_pos es _)).ne'), ?_⟩
      refine ((htail g).1.const_mul C).congr (Eventually.of_forall fun x => ?_)
      exact (hslice x).symm.trans (integral_congr_ae (Eventually.of_forall fun z =>
        (Real.norm_of_nonneg (hφ_nonneg (z, x))).symm))
    let coordinates := splitCoordinates m
    have hmp : MeasurePreserving coordinates.symm := (measurePreserving_splitCoordinates m).symm
    let ψ (z : Fin (m + 1) → ℂ) :=
      ((modulusSpherical n ds).val
        ((StrictSwapChain.cons pre post d e hn i j hi hj hre tail).chartProduct z * g)).re
    have hcomp : ψ ∘ coordinates.symm = φ := by
      funext z
      simp [ψ, φ, coordinates, splitCoordinates_symm, chartProduct, mul_assoc]
    have hψcomp : Integrable (ψ ∘ coordinates.symm) := hcomp.symm ▸ hφint
    change Integrable ψ ∧ (∫ z, ψ z) = _
    refine ⟨(hmp.integrable_comp_emb coordinates.symm.measurableEmbedding).mp hψcomp, ?_⟩
    rw [← hmp.integral_comp']
    change (∫ z, (ψ ∘ coordinates.symm) z) = _
    rw [hcomp]
    change (∫ z, φ z ∂((volume : Measure ℂ).prod volume)) = _
    rw [integral_prod_symm φ hφint]
    simp_rw [hslice]
    rw [integral_const_mul, (htail g).2, mul_assoc]

/-- Every smooth standard vector is absolutely integrable on the product of the
charts, also after right translation by an arbitrary group element. -/
theorem integrable_eval_chartProduct (w : StrictSwapChain n ds es m)
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds)
    (g : Langlands.GeneralLinear n ℂ) :
    Integrable (fun z => f (w.chartProduct z * g)) := by
  obtain ⟨C, _, hC⟩ := exists_norm_le_mul_modulusSpherical hf
  obtain ⟨_, _, hP⟩ := w.integrable_modulusSpherical
  exact ((hP g).1.const_mul C).mono'
    (hf.1.continuous.comp (w.continuous_chartProduct.mul continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun z => hC (w.chartProduct z * g))

/-- Composition of the individual strict adjacent intertwiners along a chain. -/
def intertwiner : {ds es : List ComplexCharacterData} → {m : ℕ} →
    StrictSwapChain n ds es m → (KFs n ds →ₗ[ℂ] KFs n es)
  | _, _, _, .nil _ => LinearMap.id
  | _, _, _, .cons pre post d e hn _ _ hi hj hre tail =>
      tail.intertwiner ∘ₗ (exists_strictSwapIntertwining_apply hj pre post d e hn hi hre).choose

theorem isComplexStandardIntertwining (w : StrictSwapChain n ds es m) :
    IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es)
      ds w.intertwiner := by
  induction w with
  | nil ds =>
    dsimp only [intertwiner]
    apply ComplexPermutation.intertwining_of_embedding
    refine ⟨fun k f => ?_, fun X f => coe_lie X f⟩
    change ((complexStandardRep n ds (ComplexPermutation.toUnitary k) f : KFs n ds) :
      Langlands.GeneralLinear n ℂ → ℂ) = _
    rw [principalSeriesRep_apply_coe, ComplexPermutation.toUnits_toUnitary]
    rfl
  | @cons pre post d e hn i j hi hj hre fs m tail ih =>
    dsimp only [intertwiner]
    have h := (exists_strictSwapIntertwining_apply hj pre post d e hn hi hre).choose_spec.2.1
    exact h.comp tail.intertwiner ih.map_rep (fun X f => ih.map_lie (1 ⊗ₜ X) f)

set_option maxHeartbeats 800000 in
/-- The composite intertwiner is the absolutely convergent integral over the
product chart. -/
theorem intertwiner_apply (w : StrictSwapChain n ds es m) (g : Langlands.GeneralLinear n ℂ)
    (f : KFs n ds) :
    (w.intertwiner f).val g = ∫ z, f.val (w.chartProduct z * g) := by
  induction w generalizing g with
  | nil ds =>
    simp only [intertwiner, LinearMap.id_apply, chartProduct, one_mul, integral_emptyCoordinates]
  | @cons pre post d e hn i j hi hj hre fs m tail ih =>
    let head := (exists_strictSwapIntertwining_apply hj pre post d e hn hi hre).choose
    have hhead := (exists_strictSwapIntertwining_apply hj pre post d e hn hi hre).choose_spec.2.2
    let chain := StrictSwapChain.cons pre post d e hn i j hi hj hre tail
    let φ (z : ℂ × (Fin m → ℂ)) :=
      f.val (chart i j hj z.1 * (tail.chartProduct z.2 * g))
    let ψ (z : Fin (m + 1) → ℂ) := f.val (chain.chartProduct z * g)
    let coordinates := splitCoordinates m
    have hmp : MeasurePreserving coordinates.symm := (measurePreserving_splitCoordinates m).symm
    have hcomp : ψ ∘ coordinates.symm = φ := by
      funext z
      simp [ψ, φ, chain, coordinates, splitCoordinates_symm, chartProduct, mul_assoc]
    have hψint : Integrable ψ := chain.integrable_eval_chartProduct (mem_of_mem_kFs f.2) g
    have hφint : Integrable φ :=
      hcomp ▸ (hmp.integrable_comp_emb coordinates.symm.measurableEmbedding).mpr hψint
    change (tail.intertwiner (head f)).val g = ∫ z, ψ z
    rw [ih, ← hmp.integral_comp']
    change (∫ x, (head f).val (tail.chartProduct x * g)) = ∫ z, (ψ ∘ coordinates.symm) z
    rw [hcomp]
    change _ = ∫ z, φ z ∂((volume : Measure ℂ).prod volume)
    rw [integral_prod_symm φ hφint]
    exact integral_congr_ae (Eventually.of_forall fun x => hhead (tail.chartProduct x * g) f)

/-- Concatenation of two composable chains. -/
def append {fs : List ComplexCharacterData} {k : ℕ} :
    {ds es : List ComplexCharacterData} → {m : ℕ} →
    StrictSwapChain n ds es m → StrictSwapChain n es fs k → StrictSwapChain n ds fs (k + m)
  | _, _, _, .nil _, v => v
  | _, _, _, .cons pre post d e hn i j hi hj hre tail, v =>
      .cons pre post d e hn i j hi hj hre (append tail v)

theorem intertwiner_append {fs : List ComplexCharacterData} {k : ℕ}
    (w : StrictSwapChain n ds es m) (v : StrictSwapChain n es fs k) :
    (w.append v).intertwiner = v.intertwiner ∘ₗ w.intertwiner := by
  induction w with
  | nil => simp only [append, intertwiner, LinearMap.comp_id]
  | cons _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [append, intertwiner, ih, LinearMap.comp_assoc]

end StrictSwapChain

end Langlands.Archimedean.ComplexSwapJacquet
