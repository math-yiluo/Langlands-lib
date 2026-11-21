import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedIntegrals
import Langlands.Global.RankinSelberg.ComplexUnequalDualFamily

/-! # Mellin pair identities on genuine right translates -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexWhittakerTranslatedMellin

open Langlands.Archimedean (unitaryCompact continuous_unitary_toUnits)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open ArchimedeanMellinPair (RapidDecay)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalIwasawa (alpha continuous_alpha kpart npart npart_mul_logTorus_mul_kpart
  alpha_unipotent_mul alpha_torus_mul)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexUnequalFamily (HasLeftCharacter ordinary_halfPlaneDomination dual_halfPlaneDomination)
open ComplexUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos complexUnequalIntegrand_eq_mul
  complexUnequalDualKernel_eq_mul ComplexUnequalPairIdentity)
open ComplexWhittakerTranslatedIntegrals (weightedOrdinary weightedDual complexWhittakerTranslatedIntegrals)
open RealConvergenceAnalysis (rootPos)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Std" => Automorphic.complexStandardKFinite
local notation "R" => fun r t => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction

/-- The logarithmic displacement under a right translation is determined by the unitary factor. -/
theorem alpha_right_mul {n : ℕ} (x y : G n) :
    alpha (x * y) = alpha x + alpha ((kpart x).val * y) := by
  calc
    _ = alpha ((npart x).val * (logTorus (alpha x) * ((kpart x).val * y))) := by
      rw [← mul_assoc, ← mul_assoc, npart_mul_logTorus_mul_kpart]
    _ = _ := by rw [alpha_unipotent_mul, alpha_torus_mul]

private theorem rootPos_le_of_bounded_shift {r : ℕ} (y z : Fin (r + 1) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (h : ∀ i, |z i| ≤ L) : rootPos y ≤ rootPos (y + z) + (r : ℝ) * (2 * L) := by
  unfold rootPos
  calc
    _ ≤ ∑ i : Fin r, (max ((y + z) i.castSucc - (y + z) i.succ) 0 + 2 * L) := by
      refine Finset.sum_le_sum fun i _ => max_le ?_ ?_
      · have hi := (abs_le.mp (h i.castSucc)).1
        have hj := (abs_le.mp (h i.succ)).2
        have hm := le_max_left ((y + z) i.castSucc - (y + z) i.succ) 0
        simp only [Pi.add_apply] at hm ⊢
        linarith
      · exact add_nonneg (le_max_right _ _) (mul_nonneg (by norm_num) hL)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem exists_model_simpleRootBound {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G (r + 1),
      ‖W.val g‖ ≤ C * Real.exp ((N : ℝ) * (∑ i, |alpha g i|) - (M : ℝ) * rootPos (alpha g)) := by
  obtain ⟨N, hN⟩ := complexWhittakerSimpleRootMajorization r ds a W
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hc, hC⟩ := hN M []
  refine ⟨C, hc, fun g => ?_⟩
  have he := complexWhittakerModel_left_equivariant W.2 (npart g).val (npart g).2
    (logTorus (alpha g) * (kpart g).val)
  rw [← mul_assoc, npart_mul_logTorus_mul_kpart] at he
  rw [he, norm_mul]
  simpa only [complexWhittakerCharacter, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex,
    one_mul, List.map_nil, List.prod_nil, Module.End.one_apply, rootPos] using hC (alpha g) (kpart g)

/-- A compact family of genuine right translates has common growth order and arbitrary
simple-root decay. -/
theorem compact_rightTranslate_uniformSimpleRootBound {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) (S : Set (G (r + 1))) (hS : IsCompact S) :
    HasUniformSimpleRootBound S (fun s g => W.val (g * s)) := by
  let U := unitaryCompact ℂ (r + 1)
  let F := fun p : U × G (r + 1) => ∑ i, |alpha (p.1.val * p.2) i|
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp (continuous_alpha.comp
      ((continuous_subtype_val.comp continuous_fst).mul continuous_snd))).abs
  obtain ⟨L₀, hBound⟩ := (isCompact_univ.prod hS).exists_bound_of_continuousOn hF.continuousOn
  let L := max L₀ 0
  have hL : 0 ≤ L := le_max_right _ _
  have hb (k : U) (s : G (r + 1)) (hs : s ∈ S) : (∑ i, |alpha (k.val * s) i|) ≤ L := by
    have hh := hBound (k, s) ⟨mem_univ k, hs⟩
    change ‖∑ i, |alpha (k.val * s) i|‖ ≤ L₀ at hh
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hh
    exact hh.trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_model_simpleRootBound W
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hW⟩ := hN J
  let E : ℝ := (N : ℝ) * L + (J : ℝ) * (r : ℝ) * (2 * L)
  refine ⟨C * Real.exp E, mul_nonneg hC (Real.exp_nonneg _), fun s hs g => ?_⟩
  let y := alpha g
  let z := alpha ((kpart g).val * s)
  have hz : (∑ i, |z i|) ≤ L := hb (kpart g) s hs
  have hzi (i : Fin (r + 1)) : |z i| ≤ L :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i)).trans hz
  have hLen : (∑ i, |(y + z) i|) ≤ (∑ i, |y i|) + L := by
    rw [← add_le_add_iff_left (∑ i, |y i|)] at hz
    apply le_trans ?_ hz
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => abs_add_le _ _
  have hRoot := rootPos_le_of_bounded_shift y z L hL hzi
  have hh₁ := mul_le_mul_of_nonneg_left hLen (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hh₂ := mul_le_mul_of_nonneg_left hRoot (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  have hExp : (N : ℝ) * (∑ i, |(y + z) i|) - (J : ℝ) * rootPos (y + z) ≤
      (N : ℝ) * (∑ i, |y i|) - (J : ℝ) * rootPos y + E := by
    dsimp only [E]
    nlinarith only [hh₁, hh₂]
  refine (hW (g * s)).trans ?_
  rw [alpha_right_mul]
  change C * Real.exp ((N : ℝ) * (∑ i, |(y + z) i|) - (J : ℝ) * rootPos (y + z)) ≤ _
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) hC).trans_eq ?_
  rw [Real.exp_add]
  change _ = C * Real.exp E * Real.exp ((N : ℝ) * (∑ i, |y i|) - (J : ℝ) * rootPos y)
  ring

private theorem norm_weight_mul_le {δ : ℝ} (hδ : 0 < δ) (f : ℝ → ℂ) {C τ : ℝ}
    (hf : ‖f δ‖ ≤ C * δ ^ τ) (z : ℂ) : ‖z * f δ‖ ≤ C * ‖z * (δ : ℂ) ^ (τ : ℂ)‖ := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hδ, Complex.ofReal_re]
  calc
    _ ≤ ‖z‖ * (C * δ ^ τ) := mul_le_mul_of_nonneg_left hf (norm_nonneg _)
    _ = _ := by ring

/-- Both rapidly weighted kernels for fixed translates have integrable bounds uniform in the
additional compact parameters used in their finite-model approximations. -/
theorem exists_compact_mellin_bounds {r t : ℕ} (h : t < r) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel t es (-a)) (g : G (r + 1)) (g' : G (t + 1))
    (f f' : ℝ → ℂ) (hf : RapidDecay f) (hf' : RapidDecay f') :
    ∃ (M : Q t → ℝ) (M' : Q t × R r t → ℝ),
      Integrable M D.measure ∧ Integrable M' (complexUnequalDualMeasure (r := r) a D) ∧
      (∀ q (k : KU (r + 1)) (l : KU (t + 1)),
        ‖weightedOrdinary h (ρ (Unitary.toUnits k * g) W.val) (ρ (Unitary.toUnits l * g') V.val) f q‖ ≤ M q) ∧
      (∀ p (k : KU (r + 1)) (l : KU (t + 1)),
        ‖weightedDual h (ρ (Unitary.toUnits k * g) W.val) (ρ (Unitary.toUnits l * g') V.val) f' p‖ ≤ M' p) := by
  let T := (KU (r + 1) × KU (t + 1)) × ℂ
  let A := fun p : T => ρ (Unitary.toUnits p.1.1 * g) W.val
  let B := fun p : T => ρ (Unitary.toUnits p.1.2 * g') V.val
  let s : T → ℂ := Prod.snd
  let S₁ := Set.range fun k : KU (r + 1) => Unitary.toUnits k * g
  let S₂ := Set.range fun k : KU (t + 1) => Unitary.toUnits k * g'
  have hS₁ : IsCompact S₁ := isCompact_range (continuous_unitary_toUnits.mul_const g)
  have hS₂ : IsCompact S₂ := isCompact_range (continuous_unitary_toUnits.mul_const g')
  have hA (p : T) : HasLeftCharacter a (A p) := by
    intro u x
    dsimp only [A, ArchimedeanLocal.translateFunction]
    rw [mul_assoc, complexWhittakerModel_left_equivariant W.2 _ u.2]
  have hB (p : T) : HasLeftCharacter (-a) (B p) := by
    intro u x
    dsimp only [B, ArchimedeanLocal.translateFunction]
    rw [mul_assoc, complexWhittakerModel_left_equivariant V.2 _ u.2]
  have hA₀ : HasUniformSimpleRootBound Set.univ A := by
    obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound W S₁ hS₁
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hW⟩ := hN J
    exact ⟨C, hC, fun p _ => hW _ ⟨p.1.1, rfl⟩⟩
  have hB₀ : HasUniformSimpleRootBound Set.univ B := by
    obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound V S₂ hS₂
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hV⟩ := hN J
    exact ⟨C, hC, fun p _ => hV _ ⟨p.1.2, rfl⟩⟩
  obtain ⟨σ, hOrd⟩ := ordinary_halfPlaneDomination h D Set.univ A B s hA hB hA₀ hB₀
  obtain ⟨σ', hDual⟩ := dual_halfPlaneDomination h a D Set.univ A B s hA hB hA₀ hB₀
  let τ := σ + 1
  let τ' := σ' + 1
  obtain ⟨N, hN, hNbound⟩ := hOrd τ
  obtain ⟨N', hN', hN'bound⟩ := hDual τ'
  obtain ⟨C, hC⟩ := hf τ
  obtain ⟨C', hC'⟩ := hf' τ'
  have hC₀ := RapidDecay.nonneg_const hC
  have hC'₀ := RapidDecay.nonneg_const hC'
  refine ⟨C • N, C' • N', hN.const_mul C, hN'.const_mul C', ?_, ?_⟩
  · intro q k l
    let p : T := ((k, l), (τ : ℂ))
    have hp : σ < (s p).re := by dsimp [s, p, τ]; linarith
    have hz : (s p).re ≤ τ := by simp [s, p]
    have hb := hNbound p (mem_univ p) hp hz q
    have hc := norm_weight_mul_le (quotientDetAbs_pos q) f (hC _ (quotientDetAbs_pos q))
      (complexUnequalIntegrand h (A p) (B p) 0 q)
    rw [← complexUnequalIntegrand_eq_mul] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hb hC₀)
  · intro x k l
    let p : T := ((k, l), (τ' : ℂ))
    have hp : σ' < (s p).re := by dsimp [s, p, τ']; linarith
    have hz : (s p).re ≤ τ' := by simp [s, p]
    have hb := hN'bound p (mem_univ p) hp hz x
    have hc := norm_weight_mul_le (quotientDetAbs_pos x.1) f' (hC' _ (quotientDetAbs_pos x.1))
      (complexUnequalDualKernel h (A p) (B p) 0 x)
    rw [← complexUnequalDualKernel_eq_mul] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hb hC'₀)

/-- The radial Mellin pair identities on the finite model imply the exact pair identities
on arbitrary fixed right translates of intertwiner values. -/
def ComplexWhittakerTranslatedMellinStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData t),
    (∀ (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
      ComplexUnequalPairIdentity h ds es a D W.val V.val) →
    ∀ (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)) (B' : Std (t + 1) es →ₗ[ℂ] (G (t + 1) → ℂ)),
      IsComplexWhittakerIntertwiner r ds a B → IsComplexWhittakerIntertwiner t es (-a) B' →
    ∀ (v : Std (r + 1) ds) (v' : Std (t + 1) es) (g : G (r + 1)) (g' : G (t + 1)),
      ComplexUnequalPairIdentity h ds es a D (ρ g (B v)) (ρ g' (B' v'))

theorem complexWhittakerTranslatedMellin : ComplexWhittakerTranslatedMellinStatement := by
  intro r t h ds es a D hPair B B' hB hB' v v' g g' b f f' hf hf' hfd hf'd hMellin hMellin'
  let W : complexWhittakerModel r ds a :=
    ⟨B v, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)⟩
  let V : complexWhittakerModel t es (-a) :=
    ⟨B' v', Submodule.mem_iSup_of_mem B' (Submodule.mem_iSup_of_mem hB' ⟨v', rfl⟩)⟩
  obtain ⟨M, M', hM, hM', hBound, hBound'⟩ := exists_compact_mellin_bounds h ds es a D W V g g' f f' hfd hf'd
  exact complexWhittakerTranslatedIntegrals r t h ds es a D f f' hf hf'
    (fun U V => hPair U V b f f' hf hf' hfd hf'd hMellin hMellin')
    B B' hB hB' v v' g g' M M' hM hM' hBound hBound'

end Langlands.Global.RankinSelbergGlobal.ComplexWhittakerTranslatedMellin
