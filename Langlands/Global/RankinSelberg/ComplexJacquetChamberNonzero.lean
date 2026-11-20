import Langlands.Global.RankinSelberg.ComplexJacquetChamberIntertwiner
import Langlands.Global.RankinSelberg.ComplexLocalDualWhittakerGauge
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-! # Nonvanishing of the complex open-cell Whittaker functional in the strict chamber -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberNonzero

open Langlands.Archimedean (complexStandardModule complexPositionCharacter unitaryCompact)
open Langlands.Archimedean.ComplexDuality (isCompact_unitaryCompact)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (mul_conjTranspose_one)
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexLocalIwasawa (alpha kpart continuous_kpart npart npart_mul_logTorus_mul_kpart kpart_iwasawa
  conjTorus conjTorus_val logTorus_neg)

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => GeneralLinear.upperUnipotent n ℂ
local notation "UC" => unitaryCompact ℂ n
local notation "B" => upperTriangularSubgroup n ℂ
local notation "w" => weylLong n ℂ
local notation "Cell" => UpperBruhatCell n ℂ Fin.revPerm

private def pivotProduct (k : G) : ℝ := ∏ i : Fin n, ‖k.val i i.rev‖ ^ 2

private theorem pivotProduct_nonneg (k : G) : 0 ≤ pivotProduct k :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

private theorem continuous_pivotProduct : Continuous (pivotProduct (n := n)) := by
  unfold pivotProduct
  exact continuous_finsetProd _ fun i _ => (GeneralLinear.entry i i.rev).continuous.norm.pow _

private theorem row_norm_sq (k : UC) (i : Fin n) : (∑ j, ‖k.val.val i j‖ ^ 2) = 1 := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i) (mul_conjTranspose_one k)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj', Matrix.one_apply_eq] at h
  exact_mod_cast h

private theorem entry_norm_sq_le_one (k : UC) (i j : Fin n) : ‖k.val.val i j‖ ^ 2 ≤ 1 := by
  rw [← row_norm_sq k i]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖k.val.val i j‖) (Finset.mem_univ j)

private theorem pivotProduct_le_one (k : UC) : pivotProduct k.val ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => sq_nonneg _) (fun i _ => entry_norm_sq_le_one k i i.rev)

private theorem mul_weylLong_mem_upper_of_pivotProduct_eq_one (k : UC)
    (hk : pivotProduct k.val = 1) : k.val * w ∈ B := by
  have hdiag (i : Fin n) : ‖k.val.val i i.rev‖ ^ 2 = 1 := by
    let p (j : Fin n) := ‖k.val.val j j.rev‖ ^ 2
    have hprod := Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)
    change p i * (∏ j ∈ Finset.univ.erase i, p j) = pivotProduct k.val at hprod
    have hle : (∏ j ∈ Finset.univ.erase i, p j) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => sq_nonneg _) (fun j _ => entry_norm_sq_le_one k j j.rev)
    apply le_antisymm (entry_norm_sq_le_one k i i.rev)
    rw [← hk, ← hprod]
    exact mul_le_of_le_one_right (sq_nonneg _) hle
  intro i j hji
  change (k.val * w) i j = 0
  rw [mul_weylLong_entry]
  have hsum : (∑ l ∈ Finset.univ.erase i.rev, ‖k.val.val i l‖ ^ 2) = 0 := by
    have h := Finset.add_sum_erase Finset.univ (fun l => ‖k.val.val i l‖ ^ 2) (Finset.mem_univ i.rev)
    rw [hdiag i, row_norm_sq] at h
    linarith
  have hmem : j.rev ∈ Finset.univ.erase i.rev :=
    Finset.mem_erase.mpr ⟨fun h => hji.ne (Fin.rev_injective h), Finset.mem_univ _⟩
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg ‖k.val.val i l‖)).mp hsum _ hmem
  exact norm_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hz)

private def cellCoordinate (c : Cell) : N :=
  let u := (UpperBruhatCoordinates.cellHomeomorph Fin.revPerm).symm c |>.2
  ⟨u.val, u.property.1⟩

private theorem continuous_cellCoordinate : Continuous (cellCoordinate (n := n)) := by
  let e := (UpperBruhatCoordinates.cellHomeomorph Fin.revPerm (n := n) (K := ℂ)).symm
  have h : Continuous (fun c : Cell => (e c).2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp e.continuous)
  exact h.subtype_mk _

private theorem cellCoordinate_apply_map (b : B) (u : permutationUnipotentMinus n ℂ Fin.revPerm) :
    cellCoordinate (upperBruhatCellMap n ℂ Fin.revPerm (b, u)) = (⟨u.val, u.property.1⟩ : N) := by
  rw [← UpperBruhatCoordinates.cellHomeomorph_apply]
  apply Subtype.ext
  exact congrArg (fun p : B × permutationUnipotentMinus n ℂ Fin.revPerm => p.2.val)
    ((UpperBruhatCoordinates.cellHomeomorph Fin.revPerm).symm_apply_apply (b, u))

private def minusOfUpper (u : N) : permutationUnipotentMinus n ℂ Fin.revPerm :=
  ⟨u.val, (mem_permutationUnipotentMinus_iff_entries n ℂ Fin.revPerm _).2
    ⟨u.property, fun _ _ hij => UpperUnipotent.entry_eq_zero u (Fin.rev_lt_rev.mp hij)⟩⟩

private def upperPart (g : G) : B :=
  ⟨(npart g).val * logTorus (alpha g),
    mul_mem (upperUnipotent_le_upperTriangular n ℂ (npart g).property)
      (diagonalUnits_mem_upperTriangular n _)⟩

private def compactPartCell (u : N) : Cell :=
  upperBruhatCellMap n ℂ Fin.revPerm ((upperPart (w * u.val))⁻¹, minusOfUpper u)

private theorem compactPartCell_val (u : N) : (compactPartCell u).val = (kpart (w * u.val)).val := by
  have h := npart_mul_logTorus_mul_kpart (w * u.val)
  change (upperPart (w * u.val)).val * (kpart (w * u.val)).val = w * u.val at h
  let b := (upperPart (w * u.val)).val
  calc
    _ = b⁻¹ * (w * u.val) := mul_assoc _ _ _
    _ = b⁻¹ * (b * (kpart (w * u.val)).val) := congrArg (fun x => b⁻¹ * x) h.symm
    _ = _ := inv_mul_cancel_left _ _

private theorem cellCoordinate_compactPartCell (u : N) : cellCoordinate (compactPartCell u) = u :=
  cellCoordinate_apply_map _ _

private theorem cellCoordinate_of_pivotProduct_eq_one (k : UC) (hk : pivotProduct k.val = 1) :
    ∃ c : Cell, c.val = k.val ∧ cellCoordinate c = 1 := by
  let b : B := ⟨k.val * w, mul_weylLong_mem_upper_of_pivotProduct_eq_one k hk⟩
  refine ⟨upperBruhatCellMap n ℂ Fin.revPerm (b, 1), ?_, cellCoordinate_apply_map b 1⟩
  change k.val * w * w * 1 = k.val
  rw [mul_one, mul_assoc, weylLong_mul_self, mul_one]

private def openCellWeight (u : N) : ℝ := pivotProduct (kpart (w * u.val)).val

private theorem continuous_openCellWeight : Continuous (openCellWeight (n := n)) :=
  continuous_pivotProduct.comp (continuous_subtype_val.comp (continuous_kpart.comp
    (continuous_const.mul continuous_subtype_val)))

private theorem openCellWeight_one : openCellWeight (1 : N) = 1 := by
  let κ : UC := ⟨w, ComplexLocalDualWhittakerGauge.weylLong_mem_unitary n⟩
  have hw : kpart w = κ := by
    have hz : logTorus (0 : Fin n → ℝ) = 1 := by
      apply Units.ext
      ext i j
      simp
    simpa only [Subgroup.coe_one, hz, mul_one, one_mul] using
      kpart_iwasawa (1 : N) (0 : Fin n → ℝ) κ
  simp only [openCellWeight, Subgroup.coe_one, mul_one, hw, pivotProduct]
  refine Finset.prod_eq_one fun i _ => ?_
  change ‖w i i.rev‖ ^ 2 = 1
  simp [weylLong_entry]

private theorem exists_uniform_pivotProduct_bound {U : Set N} (hU : IsOpen U) (h1 : (1 : N) ∈ U) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ u ∉ U, openCellWeight u ≤ c := by
  let image : Set G := (fun u : N => (kpart (w * u.val)).val) '' Uᶜ
  let S := closure image
  have hS : S ⊆ UC := closure_minimal (by rintro _ ⟨u, _, rfl⟩; exact (kpart _).2)
    (isCompact_unitaryCompact n).isClosed
  have hcompact : IsCompact S := (isCompact_unitaryCompact n).of_isClosed_subset isClosed_closure hS
  have himage : image = (Subtype.val : Cell → G) '' (compactPartCell '' Uᶜ) := by
    rw [image_image]
    exact image_congr fun u _ => (compactPartCell_val u).symm
  have hlt (g : G) (hg : g ∈ S) : pivotProduct g < 1 := by
    let k : UC := ⟨g, hS hg⟩
    apply lt_of_le_of_ne (pivotProduct_le_one k)
    intro he
    obtain ⟨x, hx, hδ⟩ := cellCoordinate_of_pivotProduct_eq_one k he
    have hx' : x ∈ closure (compactPartCell '' Uᶜ) := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, ← himage]
      simpa only [mem_preimage, hx] using hg
    have hsub : compactPartCell '' Uᶜ ⊆ cellCoordinate ⁻¹' Uᶜ := by
      rintro _ ⟨u, hu, rfl⟩
      rwa [mem_preimage, cellCoordinate_compactPartCell]
    have hbad := closure_minimal hsub (hU.isClosed_compl.preimage continuous_cellCoordinate) hx'
    exact (show cellCoordinate x ∉ U from hbad) (hδ ▸ h1)
  by_cases hne : S.Nonempty
  · obtain ⟨g, hg, hmax⟩ := hcompact.exists_isMaxOn hne continuous_pivotProduct.continuousOn
    exact ⟨pivotProduct g, pivotProduct_nonneg g, hlt g hg,
      fun u hu => hmax (subset_closure (mem_image_of_mem _ hu))⟩
  · exact ⟨0, le_rfl, zero_lt_one, fun u hu =>
      (hne ⟨_, subset_closure (mem_image_of_mem _ hu)⟩).elim⟩

section Concentration

attribute [local instance] ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "N₊" => GeneralLinear.upperUnipotent (r + 1) ℂ

private theorem exists_pos_integral_pow (ν : Measure N₊) [ν.IsHaarMeasure]
    {F : N₊ → ℂ} (hF : Continuous F) (hi : Integrable F ν) (hF₁ : F 1 = 1) :
    ∃ j : ℕ, 0 < (∫ u, F u * (openCellWeight u : ℂ) ^ j ∂ν).re := by
  let U : Set N₊ := {u | 1 / 2 < (F u).re}
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hF)
  have hU₁ : (1 : N₊) ∈ U := by simpa [U, hF₁] using (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨c, hc, hc₁, hcB⟩ := exists_uniform_pivotProduct_bound hU hU₁
  let d := (c + 1) / 2
  have hd₀ : 0 < d := by dsimp [d]; linarith
  have hcd : c < d := by dsimp [d]; linarith
  have hd₁ : d < 1 := by dsimp [d]; linarith
  let V : Set N₊ := U ∩ {u | d < openCellWeight u}
  have hV : IsOpen V := hU.inter (isOpen_lt continuous_const continuous_openCellWeight)
  have hV₁ : (1 : N₊) ∈ V := ⟨hU₁, by simpa only [mem_ofPred_eq, openCellWeight_one] using hd₁⟩
  let : LocallyCompactSpace N₊ :=
    (upperEntryCoordinates (K := ℂ) (r + 1)).isClosedEmbedding.locallyCompactSpace
  obtain ⟨L, ⟨hL₁, hL⟩, hLV⟩ := (compact_basis_nhds (1 : N₊)).mem_iff.mp (hV.mem_nhds hV₁)
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  have hLfin : ν L ≠ ∞ := hL.measure_lt_top.ne
  have hLpos : 0 < ν.real L := ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds ν hL₁).ne' hLfin
  let A : ℝ := ∫ u, ‖F u‖ ∂ν
  have hlim : Tendsto (fun j : ℕ => A * (c / d) ^ j) atTop (𝓝 0) := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hc hd₀.le)
      ((div_lt_one hd₀).mpr hcd)
    simpa only [mul_zero] using ht.const_mul A
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ν.real L / 2 by positivity))).exists
  have hdj : 0 < d ^ j := pow_pos hd₀ j
  have hpos : 0 < ν.real L * (d ^ j / 2) - c ^ j * A := by
    change A * (c / d) ^ j < ν.real L / 2 at hj
    rw [div_pow, ← mul_div_assoc, div_lt_iff₀ hdj] at hj
    linarith [show ν.real L * (d ^ j / 2) = ν.real L / 2 * d ^ j by ring]
  let q := openCellWeight (n := r + 1)
  have hq₀ (u : N₊) : 0 ≤ q u := pivotProduct_nonneg _
  have hq₁ (u : N₊) : q u ≤ 1 := pivotProduct_le_one _
  let E : N₊ → ℝ := L.indicator (fun _ => d ^ j / 2)
  have hE : Integrable E ν := (integrableOn_const (C := d ^ j / 2) hLfin).integrable_indicator hLm
  have hdom (u : N₊) : E u - c ^ j * ‖F u‖ ≤ (F u).re * q u ^ j := by
    have htail : 0 ≤ c ^ j * ‖F u‖ := mul_nonneg (pow_nonneg hc j) (norm_nonneg _)
    by_cases hu : u ∈ U
    · have hre : (1 / 2 : ℝ) ≤ (F u).re := (show (1 / 2 : ℝ) < (F u).re from hu).le
      have hE' : E u ≤ (F u).re * q u ^ j := by
        by_cases huL : u ∈ L
        · have hqu : d ≤ q u := (show d < q u from (hLV huL).2).le
          rw [show E u = d ^ j / 2 from indicator_of_mem huL _]
          calc
            d ^ j / 2 = (1 / 2 : ℝ) * d ^ j := by ring
            _ ≤ (F u).re * q u ^ j := mul_le_mul hre (pow_le_pow_left₀ hd₀.le hqu j)
              (pow_nonneg hd₀.le j) (by linarith)
        · rw [show E u = 0 from indicator_of_notMem huL _]
          exact mul_nonneg (by linarith) (pow_nonneg (hq₀ u) j)
      linarith
    · have huL : u ∉ L := fun h => hu (hLV h).1
      rw [show E u = 0 from indicator_of_notMem huL _, zero_sub, ← mul_neg, mul_comm _ (-‖F u‖)]
      calc
        _ ≤ -‖F u‖ * q u ^ j := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (hq₀ u) (hcB u hu) j)
          (neg_nonpos.mpr (norm_nonneg _))
        _ ≤ (F u).re * q u ^ j := mul_le_mul_of_nonneg_right
          (neg_le_of_abs_le (Complex.abs_re_le_norm _)) (pow_nonneg (hq₀ u) j)
  let G₀ : N₊ → ℂ := fun u => F u * (q u : ℂ) ^ j
  have hcG : Continuous G₀ := hF.mul ((Complex.continuous_ofReal.comp continuous_openCellWeight).pow j)
  have hiG : Integrable G₀ ν := by
    refine hi.norm.mono' hcG.aestronglyMeasurable (ae_of_all _ fun u => ?_)
    change ‖F u * (q u : ℂ) ^ j‖ ≤ ‖F u‖
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hq₀ u)]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (hq₀ u) (hq₁ u))
  have hreG (u : N₊) : (G₀ u).re = (F u).re * q u ^ j := by
    simp [G₀, ← Complex.ofReal_pow, Complex.mul_re]
  have hmono := integral_mono (hE.sub (hi.norm.const_mul (c ^ j))) hiG.re (fun u => by
    change E u - c ^ j * ‖F u‖ ≤ (G₀ u).re
    rw [hreG]
    exact hdom u)
  have hreInt : (∫ u, (G₀ u).re ∂ν) = (∫ u, G₀ u ∂ν).re := integral_re hiG
  change (∫ u, E u - c ^ j * ‖F u‖ ∂ν) ≤ ∫ u, (G₀ u).re ∂ν at hmono
  rw [integral_sub hE (hi.norm.const_mul (c ^ j)), integral_const_mul, hreInt] at hmono
  have hEval : (∫ u, E u ∂ν) = ν.real L * (d ^ j / 2) := by
    simp only [E, integral_indicator_const _ hLm, smul_eq_mul]
  rw [hEval] at hmono
  exact ⟨j, hpos.trans_le hmono⟩

end Concentration

section PhaseVectors

open Langlands.Archimedean (principalSeries principalSeriesCharacter rightTranslation_mem_kFiniteFunctions_complexStandardModule)
open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent)
open Langlands.Archimedean.ComplexPartialJacquet (IsStrictlyDominant)
open Langlands.Archimedean.ComplexStrictLanglandsQuotient (complexPositionWeight complexPositionCharacter_phase isPhasePower)
open Langlands.Archimedean.ComplexJacquetNonvanishing (phaseVector phaseVector_mem phaseVector_of_mem phaseMonomial)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexJacquetChamberIntertwiner (chamberIntertwiner)
open ComplexJacquetChamberConvergence (complexJacquetOpenCellConvergence)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_isHaar)
open Langlands.LocalFactor.Archimedean (complexScaledCharacter)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

private def phaseFamily (ds : List ComplexCharacterData) (j : ℕ) (x : G) : ℂ :=
  phaseVector n (complexPositionExponent ds) (complexPositionWeight ds) (fun _ => j) (x * w)

private theorem phaseFamily_mem (ds : List ComplexCharacterData) (j : ℕ) :
    phaseFamily (n := n) ds j ∈ Automorphic.complexStandardKFinite n ds := by
  exact rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds
    (phaseVector_mem _ _ (isPhasePower ds) (complexPositionCharacter_phase ds))
    (ComplexLocalDualWhittakerGauge.weylLong_mem_unitary n)

private theorem phaseFamily_compact (ds : List ComplexCharacterData) (j : ℕ) (k : UC) :
    phaseFamily ds j k.val = phaseFamily ds 0 k.val * (pivotProduct k.val : ℂ) ^ j := by
  have hk : k.val * w ∈ UC := mul_mem k.property (ComplexLocalDualWhittakerGauge.weylLong_mem_unitary n)
  unfold phaseFamily
  rw [phaseVector_of_mem _ _ hk, phaseVector_of_mem _ _ hk]
  simp only [phaseMonomial, pivotProduct, Complex.ofReal_prod]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hentry : (k.val * w).val i i = k.val.val i i.rev := mul_weylLong_entry n ℂ k.val i i
  rw [hentry]
  simp only [pow_add, add_zero, Complex.ofReal_pow, ← Complex.mul_conj', mul_pow]
  ring

private theorem phaseFamily_eq_weight (ds : List ComplexCharacterData) (j : ℕ) (x : G) :
    phaseFamily ds j x = phaseFamily ds 0 x * (pivotProduct (kpart x).val : ℂ) ^ j := by
  let y := alpha x
  let a : Fin n → ℂˣ := fun i => Units.mk0 (Real.exp (y i) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  let u := conjTorus (-y) (npart x)
  have hx : logTorus y * u.val * (kpart x).val = x := by
    change logTorus y * (conjTorus (-y) (npart x)).val * (kpart x).val = _
    rw [conjTorus_val, logTorus_neg, inv_inv]
    calc
      _ = (npart x).val * logTorus y * (kpart x).val := by group
      _ = x := npart_mul_logTorus_mul_kpart x
  have hcov (l : ℕ) : phaseFamily ds l x = principalSeriesCharacter ℂ n (complexPositionCharacter ds) a *
      phaseFamily ds l (kpart x).val := by
    have h := (phaseFamily_mem (n := n) ds l).1.2 a u (kpart x).val
    change phaseFamily ds l (logTorus y * u.val * (kpart x).val) = _ at h
    rwa [hx] at h
  rw [hcov j, hcov 0, phaseFamily_compact, mul_assoc]

private theorem phaseFamily_w (ds : List ComplexCharacterData) : phaseFamily (n := n) ds 0 w = 1 := by
  rw [phaseFamily, weylLong_mul_self, phaseVector_of_mem _ _ (unitaryCompact ℂ n).one_mem]
  simp [phaseMonomial]

/-- The exact chamber Jacquet functional, evaluated at the identity, is nonzero. -/
def ComplexJacquetChamberNonzeroStatement : Prop :=
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (he : IsStrictlyDominant (complexPositionExponent ds) r),
    ∃ f : Automorphic.complexStandardKFinite (r + 1) ds, (chamberIntertwiner μ ds a he) f 1 ≠ 0

/-- Compact phase vectors and open-cell coordinates detect the Whittaker integral. -/
theorem complexJacquetChamberNonzero : ComplexJacquetChamberNonzeroStatement := by
  intro r μ ds a he
  let ν := entryHaar μ (r + 1)
  let : ν.IsHaarMeasure := entryHaar_isHaar μ (r + 1)
  let Gᵣ := Langlands.GeneralLinear (r + 1) ℂ
  let Nᵣ := GeneralLinear.upperUnipotent (r + 1) ℂ
  let wᵣ := weylLong (r + 1) ℂ
  let F : Nᵣ → ℂ := fun u => phaseFamily ds 0 (wᵣ * u.val) * complexWhittakerCharacter a u.val
  have hstd : phaseFamily (n := r + 1) ds 0 ∈ complexStandardModule (r + 1) ds :=
    (phaseFamily_mem ds 0).1
  have hθ : Continuous (fun u : Nᵣ => complexWhittakerCharacter a u.val) := by
    unfold complexWhittakerCharacter
    exact (complexScaledCharacter a).continuous_complex.comp
      (continuous_finsetSum _ fun i _ => (UpperUnipotent.entry i.castSucc i.succ).continuous)
  have hF : Continuous F := (hstd.1.continuous.comp (continuous_const.mul continuous_subtype_val)).mul hθ
  have hF₁ : F 1 = 1 := by
    have hs : (∑ i : Fin r, (1 : Gᵣ).val i.castSucc i.succ) = 0 :=
      Finset.sum_eq_zero fun i _ => Matrix.one_apply_ne i.castSucc_lt_succ.ne
    simp only [F, wᵣ, Subgroup.coe_one, mul_one, phaseFamily_w, complexWhittakerCharacter, hs,
      AddChar.map_zero_eq_one]
  have hi : Integrable F ν := by
    have h := complexJacquetOpenCellConvergence r μ _ _ (isPhasePower ds) he _ hstd (1 : Gᵣ)
    refine h.norm.mono' hF.aestronglyMeasurable (ae_of_all _ fun u => ?_)
    simp [F, wᵣ, complexWhittakerCharacter]
  obtain ⟨j, hj⟩ := exists_pos_integral_pow ν hF hi hF₁
  refine ⟨⟨phaseFamily ds j, phaseFamily_mem ds j⟩, ?_⟩
  have hEq : (chamberIntertwiner μ ds a he) ⟨phaseFamily ds j, phaseFamily_mem ds j⟩ 1 =
      ∫ u, F u * (openCellWeight u : ℂ) ^ j ∂ν := by
    change openCellIntegral a ν (phaseFamily ds j) 1 = _
    apply integral_congr_ae (ae_of_all _ fun u => ?_)
    change phaseFamily ds j (wᵣ * u.val * 1) * complexWhittakerCharacter a u.val =
      (phaseFamily ds 0 (wᵣ * u.val) * complexWhittakerCharacter a u.val) *
        (pivotProduct (kpart (wᵣ * u.val)).val : ℂ) ^ j
    rw [mul_one, phaseFamily_eq_weight ds j]
    ring
  rw [hEq]
  exact fun hz => hj.ne' (by rw [hz, Complex.zero_re])

end PhaseVectors

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberNonzero
