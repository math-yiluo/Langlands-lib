import Langlands.Global.RankinSelberg.ComplexStandardPairingParameterProof
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.RankinSelberg.ComplexLocalAdjacentIntegrals
import Langlands.Global.RankinSelberg.ComplexLocalNormalizedGrowth
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerDual
import Langlands.Global.RankinSelberg.ComplexUnequalJacquetConventionReduction

/-! # Changing the sign of the standard character in adjacent rank -/

noncomputable section

open MeasureTheory Filter
open Langlands.LocalFactor.Archimedean
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexLocalWhittakerDual (dualData length_dualData dualFunction_mem)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

private theorem inverseData_involutive (d : ComplexCharacterData) : d.inv.inv = d := by
  apply ComplexStandardPairing.complexCharacterData_ext
  · apply ContinuousMonoidHom.ext
    intro z
    change ((d.character z)⁻¹)⁻¹ = d.character z
    exact inv_inv _
  · exact neg_neg _
  · exact neg_neg _

private theorem inverseData_mul (d e : ComplexCharacterData) :
    (d.mul e).inv = d.inv.mul e.inv := by
  apply ComplexStandardPairing.complexCharacterData_ext
  · apply ContinuousMonoidHom.ext
    intro z
    change (d.character z * e.character z)⁻¹ = (d.character z)⁻¹ * (e.character z)⁻¹
    exact mul_inv _ _
  · exact neg_add _ _
  · exact neg_add _ _

private theorem pairBlocks_inverse (ds es : List ComplexCharacterData) :
    complexPairBlocks (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv) =
      (complexPairBlocks ds es).map ComplexCharacterData.inv := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    change (es.map ComplexCharacterData.inv).map d.inv.mul ++
        complexPairBlocks (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv) =
      (es.map d.mul ++ complexPairBlocks ds es).map ComplexCharacterData.inv
    rw [List.map_append, ih, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun e _ => (inverseData_mul d e).symm)

private theorem character_at_neg_one (d : ComplexCharacterData) :
    (d.character (-1) : ℂ) = (-1 : ℂ) ^ d.weight.natAbs := by
  rw [d.character_eq]
  have h : (((-1 : ℂˣ) : ℂ)) = -1 := rfl
  rw [h]
  simp only [norm_neg, norm_one, Complex.ofReal_one, div_one, Complex.one_cpow, mul_one]
  rcases le_total 0 d.weight with h | h
  · rw [← zpow_natCast, Int.natCast_natAbs, abs_of_nonneg h]
  · rw [zpow_eq_inv_pow_natAbs _ h]
    simp

private theorem blockEpsilon_opposite (d : ComplexCharacterData) (s : ℂ) :
    (d.epsilon (-1) 1 zero_lt_one s : ℂ) * (d.inv.epsilon 1 1 zero_lt_one (1 - s) : ℂ) = 1 := by
  have hp : Complex.I ^ d.weight.natAbs * Complex.I ^ d.weight.natAbs =
      (-1 : ℂ) ^ d.weight.natAbs := by
    rw [← mul_pow, ← pow_two, Complex.I_sq]
  simp only [ComplexCharacterData.coe_epsilon, NNReal.coe_one, Complex.ofReal_one, one_mul,
    Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.one_cpow, mul_one, map_one,
    ComplexCharacterData.inv_weight, Int.natAbs_neg]
  rw [mul_assoc, hp, character_at_neg_one, ← mul_pow]
  norm_num

private theorem listEpsilon_opposite (ds : List ComplexCharacterData) (s : ℂ) :
    (complexEpsilon ds (-1) 1 zero_lt_one s : ℂ) *
      (complexEpsilon (ds.map ComplexCharacterData.inv) 1 1 zero_lt_one (1 - s) : ℂ) = 1 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, complexEpsilon_cons, Units.val_mul]
    rw [mul_mul_mul_comm, blockEpsilon_opposite, ih, mul_one]

private theorem pairEpsilon_opposite (ds es : List ComplexCharacterData) (s : ℂ) :
    (complexPairEpsilon ds es (-1) 1 zero_lt_one s : ℂ) *
      (complexPairEpsilon (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
        1 1 zero_lt_one (1 - s) : ℂ) = 1 := by
  unfold complexPairEpsilon
  rw [pairBlocks_inverse]
  exact listEpsilon_opposite _ s

private theorem dualData_perm_inverse (ds : List ComplexCharacterData) :
    (dualData ds).Perm (ds.map ComplexCharacterData.inv) :=
  (List.reverse_perm ds).map _

private theorem map_inverse_inverse (ds : List ComplexCharacterData) :
    (ds.map ComplexCharacterData.inv).map ComplexCharacterData.inv = ds := by
  rw [List.map_map]
  exact (List.map_congr_left (fun d _ => inverseData_involutive d)).trans (List.map_id ds)

private theorem dualData_inverse_perm (ds : List ComplexCharacterData) :
    ((dualData ds).map ComplexCharacterData.inv).Perm ds := by
  simpa only [map_inverse_inverse] using (dualData_perm_inverse ds).map ComplexCharacterData.inv

private theorem centralSign_dualData (ds : List ComplexCharacterData) :
    complexCentralSign (dualData ds) = complexCentralSign ds := by
  have h (d : ComplexCharacterData) : d.inv.character (-1) = d.character (-1) := by
    change (d.character (-1))⁻¹ = _
    rw [← map_inv]
    simp
  simp [complexCentralSign, dualData, List.map_reverse, List.map_map, List.prod_reverse, Function.comp_def, h]

private theorem doubleDual {j : ℕ} (W : Langlands.GeneralLinear j ℂ → ℂ) :
    ArchimedeanLocal.dualFunction j (ArchimedeanLocal.dualFunction j W) = W :=
  funext fun g => congrArg W (GeneralLinear.weylInverseTranspose_involutive j ℂ g)

variable {r : ℕ}

local notation "gap" => Nat.lt_succ_self r
local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G" => Langlands.GeneralLinear (r + 2) ℂ
local notation "wd" => ArchimedeanLocal.dualFunction (r + 2)
local notation "ud" => ArchimedeanLocal.dualFunction (r + 1)

/-- The exact adjacent-rank local equation with the specified additive parameter. -/
def ComplexLocalAdjacentAtParameterStatement (r : ℕ) (a : ℂˣ) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
  ∀ (D : ComplexQuotientMeasureData r)
    (W : Langlands.GeneralLinear (r + 2) ℂ → ℂ) (V : Langlands.GeneralLinear (r + 1) ℂ → ℂ),
    W ∈ complexWhittakerModel (r + 1) ds a → V ∈ complexWhittakerModel r es (-a) →
    UnequalEquation (Nat.lt_succ_self r) a D W V ds es a (complexCentralSign es ^ (r + 1))

/-- The standard positive adjacent equation implies the standard negative equation by duality. -/
def ComplexLocalAdjacentOppositeStatement : Prop :=
  ComplexLocalAdjacentAtParameterStatement r 1 → ComplexLocalAdjacentAtParameterStatement r (-1)

set_option maxHeartbeats 1300000 in
theorem complexLocalAdjacentOpposite : ComplexLocalAdjacentOppositeStatement (r := r) := by
  intro h ds es hds hes D W V hW hV
  have hWd : wd W ∈ complexWhittakerModel (r + 1) (dualData ds) 1 := by
    simpa only [neg_neg] using dualFunction_mem hds hW
  have hVd : ud V ∈ complexWhittakerModel r (dualData es) (-1) := by
    simpa only [neg_neg] using dualFunction_mem hes hV
  obtain ⟨σ, M, Md, hP, hD, _, _, hM, hMd, hEq, hEqd, hFE⟩ :=
    h (dualData ds) (dualData es) ((length_dualData ds).trans hds) ((length_dualData es).trans hes)
      D (wd W) (ud V) hWd hVd
  have hO : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hI (s : ℂ) (hs : σ < s.re) : Integrable (complexUnequalIntegrand gap W V s) D.measure := by
    have hInt := (integrable_complexUnequalDualKernel_adjacent_iff 1 D (wd W) (ud V) s).mp (hD s hs)
    simpa only [doubleDual] using hInt
  have hId (s : ℂ) (hs : σ < s.re) : Integrable (complexUnequalDualKernel gap W V s)
      (complexUnequalDualMeasure (r := r + 1) (-1) D) :=
    (integrable_complexUnequalDualKernel_adjacent_iff (-1) D W V s).mpr (hP s hs)
  refine ⟨σ, Md, M, hI, hId, differentiableOn_complexUnequalIntegral_of_integrable gap D W V hO hI,
    differentiableOn_complexUnequalDualIntegral_adjacent (-1) D W V hO hId, hMd, hM, ?_, ?_, ?_⟩
  · intro s hs
    have he := hEqd s hs
    rwa [complexUnequalDualIntegral_adjacent, doubleDual, doubleDual] at he
  · intro s hs
    rw [complexUnequalDualIntegral_adjacent]
    exact hEq s hs
  · have hL := complexPairLFactor_perm (dualData_perm_inverse ds) (dualData_perm_inverse es)
    have hLd := complexPairLFactor_perm (dualData_inverse_perm ds) (dualData_inverse_perm es)
    let c := complexCentralSign es ^ (r + 1)
    change ∀ᶠ s in Filter.codiscrete ℂ,
      ((complexPairLFactor ds es).denominator s)⁻¹ * M (1 - s) =
        c * (complexPairEpsilon ds es (-1) ‖((-1 : ℂˣ) : ℂ)‖₊ (nnnorm_pos.mpr (by simp)) s : ℂ) *
          ((complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator
            (1 - s))⁻¹ * Md s
    filter_upwards [CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub hFE] with s hs
    change ((complexPairLFactor (dualData ds) (dualData es)).denominator (1 - s))⁻¹ *
        Md (1 - (1 - s)) =
      complexCentralSign (dualData es) ^ (r + 1) *
        (complexPairEpsilon (dualData ds) (dualData es) 1 ‖((1 : ℂˣ) : ℂ)‖₊
          (nnnorm_pos.mpr (by simp)) (1 - s) : ℂ) *
        ((complexPairLFactor ((dualData ds).map ComplexCharacterData.inv)
          ((dualData es).map ComplexCharacterData.inv)).denominator (1 - (1 - s)))⁻¹ * M (1 - s) at hs
    rw [hL, hLd, centralSign_dualData, sub_sub_cancel,
      complexPairEpsilon_perm (dualData_perm_inverse ds) (dualData_perm_inverse es)] at hs
    simp only [Units.val_neg, Units.val_one, nnnorm_neg, nnnorm_one] at hs ⊢
    have hC : c * c = 1 := by
      dsimp only [c]
      rw [← mul_pow, ← pow_two, complexCentralSign_sq, one_pow]
    let L := complexPairLFactor ds es
    let Ld := complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
    let E : ℂ := complexPairEpsilon ds es (-1) 1 zero_lt_one s
    let Ed : ℂ := complexPairEpsilon (ds.map ComplexCharacterData.inv)
      (es.map ComplexCharacterData.inv) 1 1 zero_lt_one (1 - s)
    change (Ld.denominator (1 - s))⁻¹ * Md s =
      c * Ed * (L.denominator s)⁻¹ * M (1 - s) at hs
    change (L.denominator s)⁻¹ * M (1 - s) =
      c * E * (Ld.denominator (1 - s))⁻¹ * Md s
    rw [mul_assoc (c * E), hs]
    have hE : E * Ed = 1 := pairEpsilon_opposite ds es s
    calc
      _ = (c * c) * (E * Ed) * ((L.denominator s)⁻¹ * M (1 - s)) := by rw [hC, hE, one_mul, one_mul]
      _ = _ := by ring

/-- The adjacent-rank normalized equation and strip bounds at a fixed parameter. -/
def ComplexLocalAdjacentGrowthAtRank (r : ℕ) (a : ℂˣ) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
  ∀ (D : ComplexQuotientMeasureData r)
    (W : Langlands.GeneralLinear (r + 2) ℂ → ℂ) (V : Langlands.GeneralLinear (r + 1) ℂ → ℂ),
    W ∈ complexWhittakerModel (r + 1) ds a → V ∈ complexWhittakerModel r es (-a) →
    HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ (r + 1))
      (complexUnequalIntegral (Nat.lt_succ_self r) D W V)
      (complexUnequalDualIntegral (Nat.lt_succ_self r) a D W V)

/-- The sign change of the standard additive character preserves the normalized strip bounds. -/
def ComplexLocalAdjacentOppositeGrowthStatement : Prop :=
  ComplexLocalAdjacentGrowthAtRank r 1 → ComplexLocalAdjacentGrowthAtRank r (-1)

theorem complexLocalAdjacentOppositeGrowth : ComplexLocalAdjacentOppositeGrowthStatement (r := r) := by
  intro h ds es hds hes D W V hW hV
  have hWd : wd W ∈ complexWhittakerModel (r + 1) (dualData ds) 1 := by
    simpa only [neg_neg] using dualFunction_mem hds hW
  have hVd : ud V ∈ complexWhittakerModel r (dualData es) (-1) := by
    simpa only [neg_neg] using dualFunction_mem hes hV
  obtain ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨σ, hR⟩, hF⟩ :=
    h (dualData ds) (dualData es) ((length_dualData ds).trans hds) ((length_dualData es).trans hes)
      D (wd W) (ud V) hWd hVd
  have hL := complexPairLFactor_perm (dualData_perm_inverse ds) (dualData_perm_inverse es)
  have hLd := complexPairLFactor_perm (dualData_inverse_perm ds) (dualData_inverse_perm es)
  refine ⟨Nd, N, hNd, hN, hNdg, hNg, ⟨σ, fun s hs => ?_⟩, ?_⟩
  · obtain ⟨hP, hD⟩ := hR s hs
    rw [hL] at hP
    rw [hLd, complexUnequalDualIntegral_adjacent, doubleDual, doubleDual] at hD
    exact ⟨hD, by rwa [complexUnequalDualIntegral_adjacent]⟩
  · intro s
    have he := hF (1 - s)
    rw [sub_sub_cancel, centralSign_dualData,
      complexPairEpsilon_perm (dualData_perm_inverse ds) (dualData_perm_inverse es)] at he
    simp only [Units.val_neg, Units.val_one, nnnorm_neg, nnnorm_one] at he ⊢
    let c := complexCentralSign es ^ (r + 1)
    let E : ℂ := complexPairEpsilon ds es (-1) 1 zero_lt_one s
    let Ed : ℂ := complexPairEpsilon (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
      1 1 zero_lt_one (1 - s)
    change Nd s = c * Ed * N (1 - s) at he
    change N (1 - s) = c * E * Nd s
    have hC : c * c = 1 := by
      dsimp only [c]
      rw [← mul_pow, ← pow_two, complexCentralSign_sq, one_pow]
    have hE : E * Ed = 1 := pairEpsilon_opposite ds es s
    calc
      N (1 - s) = (c * c) * (E * Ed) * N (1 - s) := by rw [hC, hE, one_mul, one_mul]
      _ = c * E * (c * Ed * N (1 - s)) := by ring
      _ = _ := by rw [← he]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
