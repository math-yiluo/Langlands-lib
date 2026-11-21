import Langlands.Global.RankinSelberg.RealGodementCompactApproximation
import Langlands.Global.RankinSelberg.RealGodementCompactPicture
import Langlands.Representation.Archimedean.FiniteFunctionSpaces
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # A parameter-independent compact space spanned by real Godement sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Filter MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula RealJacquetFrobenius

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "K" => unitaryCompact ℝ (m + 1)
local notation "ρ" => Whittaker.rightTranslation ℂ H

/-- Restrict a real upper vector to the orthogonal group. -/
def compactSectionRestriction : (H → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun F k := F k.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The part of a compact function space that occurs in the position principal series.
The exponent zero in the first position is a reference for the compact restriction. -/
def compactFrameSpace (p : Fin 2) (ds : List RealBlock) (W : Submodule ℂ (K → ℂ)) :
    Submodule ℂ (K → ℂ) :=
  W ⊓ (principalSeries ℝ (m + 1) (realPositionCharacter (.character (charData p 0) :: ds))).map
    compactSectionRestriction

theorem mem_compactFrameSpace_iff {p : Fin 2} {ds : List RealBlock} {W : Submodule ℂ (K → ℂ)}
    {f : K → ℂ} (z : ℂ) : f ∈ compactFrameSpace p ds W ↔
      f ∈ W ∧ ∃ F ∈ principalSeries ℝ (m + 1)
        (realPositionCharacter (.character (charData p z) :: ds)), compactSectionRestriction F = f := by
  constructor
  · rintro ⟨hf, F, hF, rfl⟩
    refine ⟨hf, leadingCompactVector p ds F z, leadingCompactVector_mem_principalSeries p ds hF z, ?_⟩
    exact funext fun k => compactPictureExtension_eqOn _ F k.property
  · rintro ⟨hf, F, hF, rfl⟩
    refine ⟨hf, leadingCompactVector p ds F 0, leadingCompactVector_mem_principalSeries p ds hF 0, ?_⟩
    exact funext fun k => compactPictureExtension_eqOn _ F k.property

private def orbitCoefficient {V : Submodule ℂ (H → ℂ)} (v : K → V) :
    Module.Dual ℂ V →ₗ[ℂ] (K → ℂ) where
  toFun L k := L (v k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every compact restriction of a K-finite vector lies in a finite-dimensional
space stable under left translations by the orthogonal group. -/
theorem exists_finite_leftStable_of_kFinite {F : H → ℂ} (hF : F ∈ kFiniteVectors ρ K) :
    ∃ W : Submodule ℂ (K → ℂ), FiniteDimensional ℂ W ∧ compactSectionRestriction F ∈ W ∧
      ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W := by
  let V : Submodule ℂ (H → ℂ) := Submodule.span ℂ (Set.range fun k : K => ρ k.val F)
  let : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hF
  let v : K → V := fun k => ⟨ρ k.val F, Submodule.subset_span ⟨k, rfl⟩⟩
  let C := orbitCoefficient v
  refine ⟨LinearMap.range C, LinearMap.finiteDimensional_range C, ?_, ?_⟩
  · refine ⟨(LinearMap.proj (1 : H)).comp V.subtype, funext fun k => ?_⟩
    change F (1 * k.val) = F k.val
    rw [one_mul]
  · rintro _ ⟨L, rfl⟩ q
    have hq : V ≤ V.comap (ρ q.val) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change ρ q.val (ρ k.val F) ∈ V
      rw [← Module.End.mul_apply, ← map_mul]
      exact (v (q * k)).property
    let R : V →ₗ[ℂ] V := ((ρ q.val).comp V.subtype).codRestrict V fun x => hq x.property
    refine ⟨L.comp R, funext fun k => ?_⟩
    change L (R (v k)) = L (v (q * k))
    congr 1
    apply Subtype.ext
    change ρ q.val (ρ k.val F) = ρ (q.val * k.val) F
    rw [map_mul, Module.End.mul_apply]

private theorem integral_mem_finite_functionSpace {A B : Type*} [MeasurableSpace A]
    (μ : Measure A) (W : Submodule ℂ (B → ℂ)) [FiniteDimensional ℂ W]
    (F : A → B → ℂ) (hF : ∀ a, F a ∈ W) (hi : ∀ b, Integrable (fun a => F a b) μ) :
    (fun b => ∫ a, F a b ∂μ) ∈ W := by
  obtain ⟨S, _, hS⟩ := FiniteFunctionSpaces.exists_finset_eval_injective (Module.finrank ℂ W) W rfl
  let E : W →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun s => (LinearMap.proj s.val).comp W.subtype
  have hE : Function.Injective E := by
    apply LinearMap.ker_eq_bot.mp
    refine LinearMap.ker_eq_bot'.mpr fun w hw => ?_
    apply Subtype.ext
    exact hS w.val w.property fun b hb => congrFun hw ⟨b, hb⟩
  obtain ⟨L, hL⟩ := E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hE)
  let P := fun a : A => E ⟨F a, hF a⟩
  have hP : Integrable P μ := Integrable.of_eval fun b => hi b.val
  let x : W := L (∫ a, P a ∂μ)
  have hx : x.val = fun b => ∫ a, F a b ∂μ := by
    funext b
    let ε : (S → ℂ) →L[ℂ] ℂ := ((LinearMap.proj b).comp (W.subtype.comp L)).toContinuousLinearMap
    change ε (∫ a, P a ∂μ) = _
    rw [← ε.integral_comp_comm hP]
    apply integral_congr_ae
    exact ae_of_all _ fun a => congrArg (fun w : W => w.val b) (LinearMap.congr_fun hL ⟨F a, hF a⟩)
  rw [← hx]
  exact x.property

private def absDetPower {n : ℕ} (z : ℂ) (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  ((|g.val.det| : ℝ) : ℂ) ^ z

private theorem continuous_absDetPower {n : ℕ} (z : ℂ) :
    Continuous (absDetPower (n := n) z) := by
  have hc : Continuous (fun g : Langlands.GeneralLinear n ℝ => |g.val.det|) :=
    Units.continuous_val.matrix_det.abs
  have hPos (g : Langlands.GeneralLinear n ℝ) : 0 < |g.val.det| := abs_pos.mpr (determinant g).ne_zero
  have h (g : Langlands.GeneralLinear n ℝ) : absDetPower z g =
      Complex.exp (((Real.log |g.val.det| : ℝ) : ℂ) * z) := by
    unfold absDetPower
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hPos g).ne'),
      ← Complex.ofReal_log (hPos g).le]
  rw [funext h]
  exact ((Complex.continuous_ofReal.comp (hc.log fun g => (hPos g).ne')).mul_const z).cexp

private theorem determinantWeight_leadingShift {n : ℕ} (p : Fin 2) (s z w : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    determinantWeight (charData p z) s g = determinantWeight (charData p w) s g * absDetPower (z - w) g := by
  let d := determinant g
  let b : ℂ := (|(d : ℝ)| : ℝ)
  change ((charData p z).character d : ℂ) * b ^ s =
    ((charData p w).character d : ℂ) * b ^ s * b ^ (z - w)
  rw [(charData p z).character_eq, (charData p w).character_eq]
  simp only [charData]
  change _ * b ^ z * b ^ s = _ * b ^ w * b ^ s * b ^ (z - w)
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr d.ne_zero)
  have hPow : b ^ z = b ^ w * b ^ (z - w) := by
    rw [← Complex.cpow_add _ _ hb, show w + (z - w) = z by ring]
  rw [hPow]
  ring

private theorem compactLowerBlock_weighted_mem {W : Submodule ℂ (K → ℂ)}
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (hFW : compactSectionRestriction F ∈ W) (h : G) (a : ℂ) :
    (fun k : K => a * F (lowerBlock h * k.val)) ∈ W := by
  obtain ⟨d, u, k, hk, hEq⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact (lowerBlock h)
  let q : K := ⟨k, hk⟩
  have hValue (k' : K) : F (lowerBlock h * k'.val) = principalSeriesCharacter ℝ (m + 1)
      (realPositionCharacter (.character c :: ds)) d * compactSectionRestriction F (q * k') := by
    rw [hEq, mul_assoc _ k, hF.2]
    rfl
  let D := principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) d
  have he : (fun k : K => a * F (lowerBlock h * k.val)) =
      (a * D) • (fun k : K => compactSectionRestriction F (q * k)) := by
    funext k'
    simp only [hValue, Pi.smul_apply, smul_eq_mul, D, mul_assoc]
  rw [he]
  exact W.smul_mem _ (hW _ hFW q)

/-- A fixed lower vector and a fixed compact full-row-rank test whose
Godement sections stay in the prescribed compact space at all exponents. -/
structure CompactSectionFamily {d : ℕ} [MeasurableSpace (Langlands.GeneralLinear d ℝ)]
    (μ : Measure (Langlands.GeneralLinear d ℝ))
    (p : Fin 2) (ds : List RealBlock) (W : Submodule ℂ (unitaryCompact ℝ (d + 1) → ℂ)) where
  lower : Langlands.GeneralLinear d ℝ → ℂ
  lower_mem : lower ∈ principalSeries ℝ d (realPositionCharacter ds)
  support : Set (Matrix (Fin d) (Fin (d + 1)) ℝ)
  support_compact : IsCompact support
  support_fullRank : ∀ x ∈ support, HasFullRowRank x
  test : Matrix (Fin d) (Fin (d + 1)) ℝ → ℂ
  test_smooth : ContDiff ℝ ∞ test
  test_zero : ∀ x ∉ support, test x = 0
  compact_mem : ∀ z : ℂ,
    compactSectionRestriction (sectionValue μ (charData p z) lower test) ∈ W

section Sections

variable [MeasurableSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))

/-- The upper compact column of a family at the selected leading exponent. -/
def CompactSectionFamily.column {p : Fin 2} {ds : List RealBlock} {W : Submodule ℂ (K → ℂ)}
    (C : CompactSectionFamily μ p ds W) (z : ℂ) : K → ℂ :=
  compactSectionRestriction (sectionValue μ (charData p z) C.lower C.test)

private theorem sectionValue_shiftOnCompact (p : Fin 2) (z w : ℂ) (f : G → ℂ)
    (test : X → ℂ) (k : K) :
    sectionValue μ (charData p z) f test k.val =
      sectionValue μ (charData p w) (fun h => f h * absDetPower (z - w) h⁻¹) test k.val := by
  have hOuter : determinantWeight (charData p z) ((m : ℂ) / 2) k.val =
      determinantWeight (charData p w) ((m : ℂ) / 2) k.val := by
    rw [determinantWeight_leadingShift p _ z w k.val]
    simp only [absDetPower, MaximalParabolicIntegration.abs_det_unitary k, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
  unfold sectionValue innerIntegral
  rw [hOuter]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ fun h => ?_
  change (f h⁻¹ * determinantWeight (charData p z) (((m : ℂ) + 1) / 2) h) * _ =
    ((f h⁻¹ * absDetPower (z - w) (h⁻¹)⁻¹) *
      determinantWeight (charData p w) (((m : ℂ) + 1) / 2) h) * _
  rw [determinantWeight_leadingShift p _ z w h]
  simp only [inv_inv]
  ring

variable [BorelSpace (Langlands.GeneralLinear m ℝ)] [IsFiniteMeasureOnCompacts μ]

/-- A Gram test from a reference upper section has all its compact Godement
restrictions in the same finite left-stable space, for any continuous lower input. -/
theorem compactGramSection_mem (p : Fin 2) (w : ℂ) (ds : List RealBlock) (W : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    {F : H → ℂ} (hF : F ∈ principalSeries ℝ (m + 1)
      (realPositionCharacter (.character (charData p w) :: ds))) (hFW : compactSectionRestriction F ∈ W)
    {S : Set M} (hS : IsCompact S) (hUnit : ∀ y ∈ S, IsUnit y) {β : M → ℝ}
    (hβ : Continuous β) (hβZero : ∀ y ∉ S, β y = 0) {f : G → ℂ} (hf : Continuous f)
    (z : ℂ) : compactSectionRestriction
      (sectionValue μ (charData p z) f (gramTest (charData p w) F β)) ∈ W := by
  let a : G → ℂ := fun h => (β (lowerGram h) : ℂ) *
    (f h⁻¹ * absDetPower (z - w) h) * absDetPower (1 / 2) h
  let B : G → K → ℂ := fun h k => a h * F (lowerBlock h * k.val)
  have hEq : compactSectionRestriction
      (sectionValue μ (charData p z) f (gramTest (charData p w) F β)) =
      fun k : K => ∫ h : G, B h k ∂μ := by
    funext k
    change sectionValue μ (charData p z) f (gramTest (charData p w) F β) k.val = _
    rw [sectionValue_shiftOnCompact μ p z w f _ k, sectionValue_gramTest μ (charData p w) ds hF]
    apply integral_congr_ae
    refine ae_of_all _ fun h => ?_
    simp only [inv_inv, rowGram_rowPoint_of_orthogonal _ k.property, B, a, absDetPower, lowerGram]
    ring
  have ha : Continuous a := ((Complex.continuous_ofReal.comp (hβ.comp continuous_lowerGram)).mul
    ((hf.comp continuous_inv).mul (continuous_absDetPower (z - w)))).mul
    (continuous_absDetPower (1 / 2))
  have hWeight : HasCompactSupport (fun h : G => (β (lowerGram h) : ℂ)) := by
    have hK := isCompact_lowerGram_preimage hS hUnit
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro h hh
    by_contra! hOutside
    exact hh (by simp [hβZero _ hOutside])
  have hS' : HasCompactSupport a := hWeight.mul_right.mul_right
  have hB (h : G) : B h ∈ W := compactLowerBlock_weighted_mem hW (charData p w) ds hF hFW h (a h)
  have hInt (k : K) : Integrable (fun h => B h k) μ := by
    have hk : Continuous (fun h : G => F (lowerBlock h * k.val)) :=
      hF.1.continuous.comp (continuous_lowerBlock.mul continuous_const)
    have hSupport : HasCompactSupport (fun h => B h k) := hS'.mul_right
    exact (ha.mul hk).integrable_of_hasCompactSupport hSupport
  exact hEq.symm ▸ integral_mem_finite_functionSpace μ W B hB hInt

private def compactGramColumn (p : Fin 2) (w : ℂ) (ds : List RealBlock) (W : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    {F : H → ℂ} (hF : F ∈ principalSeries ℝ (m + 1)
      (realPositionCharacter (.character (charData p w) :: ds))) (hFW : compactSectionRestriction F ∈ W)
    {S : Set M} (hS : IsCompact S) (hUnit : ∀ y ∈ S, IsUnit y) {β : M → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβZero : ∀ y ∉ S, β y = 0) {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    CompactSectionFamily μ p ds W where
  lower := lowerCutoff ds b
  lower_mem := (realGodementLowerCutoff m ds b hb).1
  support := rowGram ⁻¹' S
  support_compact := isCompact_rowGram_preimage hS
  support_fullRank _ hx := hasFullRowRank_of_isUnit_rowGram (hUnit _ hx)
  test := gramTest (charData p w) F β
  test_smooth := contDiff_gramTest _ _ hF hS.isClosed hUnit hβ hβZero
  test_zero _ hx := gramTest_eq_zero _ _ hβZero hx
  compact_mem := compactGramSection_mem μ p w ds W hW hF hFW hS hUnit hβ.continuous hβZero
    (realGodementLowerCutoff m ds b hb).1.1.continuous

variable [Measure.IsOpenPosMeasure μ] [Measure.IsMulRightInvariant μ]

/-- A fixed finite-dimensional space of compact restrictions is spanned at every
leading exponent by sections from fixed lower inputs and fixed compact tests. -/
def RealGodementCompactFrameStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)] [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    [Measure.IsMulRightInvariant μ] (p : Fin 2) (ds : List RealBlock)
    (W : Submodule ℂ (unitaryCompact ℝ (m + 1) → ℂ)) [FiniteDimensional ℂ W],
    (∀ f ∈ W, ∀ q : unitaryCompact ℝ (m + 1), (fun k : unitaryCompact ℝ (m + 1) => f (q * k)) ∈ W) →
    ∀ z : ℂ, Submodule.span ℂ (Set.range fun C : CompactSectionFamily μ p ds W => C.column μ z) =
      compactFrameSpace p ds W

theorem realGodementCompactFrame : RealGodementCompactFrameStatement := by
  intro m _ _ μ _ _ _ p ds W _ hW z
  let V : Submodule ℂ (unitaryCompact ℝ (m + 1) → ℂ) :=
    Submodule.span ℂ (Set.range fun C : CompactSectionFamily μ p ds W => C.column μ z)
  have hle : V ≤ compactFrameSpace p ds W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨C, rfl⟩
    apply (mem_compactFrameSpace_iff z).mpr
    refine ⟨C.compact_mem z, _, ?_, rfl⟩
    exact realGodementSection m μ (charData p z) ds C.lower C.lower_mem C.support C.support_compact
      C.support_fullRank C.test C.test_smooth C.test_zero
  refine le_antisymm hle ?_
  intro f hf
  obtain ⟨hfW, F, hF, rfl⟩ := (mem_compactFrameSpace_iff z).mp hf
  have : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le (hle.trans inf_le_left)
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose S β b hS hUnit hβ hZero hb hError using fun j : ℕ =>
    realGodementCompactApproximation m μ (charData p z) ds F hF (ε j) (hε j)
  let C (j : ℕ) : CompactSectionFamily μ p ds W :=
    compactGramColumn μ p z ds W hW hF hfW (hS j) (hUnit j) (hβ j) (hZero j) (hb j)
  have hLim : Tendsto (fun j => (C j).column μ z) atTop (𝓝 (compactSectionRestriction F)) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ => dist_nonneg) (fun j => ?_)
    rw [dist_eq_norm]
    exact (hError j k.val k.property).le
  exact V.closed_of_finiteDimensional.mem_of_tendsto hLim
    (Eventually.of_forall fun j => Submodule.subset_span ⟨C j, rfl⟩)

end Sections

end Langlands.Global.RankinSelbergGlobal.RealGodement
