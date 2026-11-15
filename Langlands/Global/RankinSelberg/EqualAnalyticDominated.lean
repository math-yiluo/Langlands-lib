import Langlands.Global.RankinSelberg.EqualAnalyticArchimedeanFourier
import Langlands.Global.RankinSelberg.EqualAnalyticFiniteAdeles

/-! # Rapidly decreasing majorants of Schwartz–Bruhat functions

A function on `𝔸^n` is *dominated* when it vanishes unless the finite coordinates lie in
`d⁻¹ Ô` for a fixed nonzero `d ∈ 𝒪`, and decays faster than every power of the archimedean
coordinates. Every Schwartz–Bruhat function is continuous, integrable for the covolume-one
measure and dominated.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

local instance dominatedMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance dominatedBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance dominatedFiniteMeasurableSpace : MeasurableSpace (FiniteAdeles F) := borel _

local instance dominatedFiniteBorelSpace : BorelSpace (FiniteAdeles F) := ⟨rfl⟩

local instance dominatedFiniteSecondCountable : SecondCountableTopology (FiniteAdeles F) :=
  finiteAdeles_secondCountableTopology F

local instance dominatedFiniteLocallyCompact : LocallyCompactSpace (FiniteAdeles F) :=
  finiteAdeles_locallyCompactSpace F

/-- `Φ` vanishes unless the finite coordinates lie in `d⁻¹ Ô` for some nonzero `d ∈ 𝒪`, and
decays faster than every power of the archimedean coordinates. -/
def IsRowDominated (n : ℕ) (Φ : RowVector F n → ℂ) : Prop :=
  ∃ d : 𝓞 F, d ≠ 0 ∧
    (∀ x, Φ x ≠ 0 → ∀ j, algebraMap (𝓞 F) (FiniteAdeles F) d * finiteCoordinates F n x j ∈
      integralFiniteAdeles F) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖archimedeanCoordinates F n x‖) ^ N * ‖Φ x‖ ≤ C

variable {F}

theorem isRowDominated_zero (n : ℕ) : IsRowDominated F n 0 :=
  ⟨1, one_ne_zero, fun x hx => (hx rfl).elim, fun N => ⟨0, fun x => by simp⟩⟩

theorem IsRowDominated.add {n : ℕ} {Φ Ψ : RowVector F n → ℂ} (hΦ : IsRowDominated F n Φ)
    (hΨ : IsRowDominated F n Ψ) : IsRowDominated F n (Φ + Ψ) := by
  obtain ⟨d, hd, hds, hdec⟩ := hΦ
  obtain ⟨d', hd', hds', hdec'⟩ := hΨ
  refine ⟨d * d', mul_ne_zero hd hd', fun x hx j => ?_, fun N => ?_⟩
  · rw [map_mul]
    by_cases h : Φ x = 0
    · have h' : Ψ x ≠ 0 := by
        intro h'
        apply hx
        simp [h, h']
      rw [mul_assoc]
      exact mul_mem (algebraMap_ringOfIntegers_mem F d) (hds' x h' j)
    · rw [mul_comm (algebraMap _ _ d), mul_assoc]
      exact mul_mem (algebraMap_ringOfIntegers_mem F d') (hds x h j)
  · obtain ⟨C, hC⟩ := hdec N
    obtain ⟨C', hC'⟩ := hdec' N
    refine ⟨C + C', fun x => ?_⟩
    have hn : 0 ≤ (1 + ‖archimedeanCoordinates F n x‖) ^ N := by positivity
    calc (1 + ‖archimedeanCoordinates F n x‖) ^ N * ‖(Φ + Ψ) x‖ ≤
        (1 + ‖archimedeanCoordinates F n x‖) ^ N * (‖Φ x‖ + ‖Ψ x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hn
      _ = _ + _ := mul_add _ _ _
      _ ≤ C + C' := add_le_add (hC x) (hC' x)

theorem IsRowDominated.smul {n : ℕ} {Φ : RowVector F n → ℂ} (hΦ : IsRowDominated F n Φ)
    (c : ℂ) : IsRowDominated F n (c • Φ) := by
  obtain ⟨d, hd, hds, hdec⟩ := hΦ
  refine ⟨d, hd, fun x hx j => hds x (fun h => hx (by simp [h])) j, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hdec N
  refine ⟨‖c‖ * C, fun x => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

variable (F)

theorem continuous_archimedeanCoordinates (n : ℕ) :
    Continuous (archimedeanCoordinates F n) :=
  continuous_fst.comp (rowSplit F n).continuous

theorem continuous_finiteCoordinates (n : ℕ) : Continuous (finiteCoordinates F n) :=
  continuous_snd.comp (rowSplit F n).continuous

/-- A Schwartz function decays faster than every power. -/
theorem SchwartzMap.exists_one_add_pow_mul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : SchwartzMap E ℂ) (N : ℕ) :
    ∃ C : ℝ, ∀ e, (1 + ‖e‖) ^ N * ‖f e‖ ≤ C := by
  obtain ⟨C₀, -, hC₀⟩ := f.decay 0 0
  obtain ⟨C₁, -, hC₁⟩ := f.decay N 0
  refine ⟨2 ^ N * (C₀ + C₁), fun e => ?_⟩
  have h0 := hC₀ e
  have h1 := hC₁ e
  rw [norm_iteratedFDeriv_zero] at h0 h1
  simp only [pow_zero, one_mul] at h0
  calc (1 + ‖e‖) ^ N * ‖f e‖ ≤ 2 ^ N * (1 + ‖e‖ ^ N) * ‖f e‖ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le _ (norm_nonneg _) N) (norm_nonneg _)
    _ = 2 ^ N * (‖f e‖ + ‖e‖ ^ N * ‖f e‖) := by ring
    _ ≤ 2 ^ N * (C₀ + C₁) := by gcongr

/-- Pure Schwartz–Bruhat tensors are continuous, integrable and dominated. -/
theorem isPureSchwartzBruhat_properties (n : ℕ) [CompactSpace (AdeleQuotient F)]
    {Φ : RowVector F n → ℂ} (hΦ : IsPureSchwartzBruhat F n Φ) :
    Continuous Φ ∧ Integrable Φ (rectangleMeasure F 1 n) ∧ IsRowDominated F n Φ := by
  obtain ⟨Φinf, Φfin, hlc, hcs, rfl⟩ := hΦ
  have hfc : Continuous Φfin := hlc.continuous
  refine ⟨(Φinf.continuous.comp (continuous_archimedeanCoordinates F n)).mul
    (hfc.comp (continuous_finiteCoordinates F n)), ?_, ?_⟩
  · exact integrable_rect_tensor F n Φinf.integrable (hfc.integrable_of_hasCompactSupport hcs)
  · -- the compact support lies in `d⁻¹ Ô` coordinatewise
    have hK : IsCompact (⋃ j : Fin n, (fun a : FinRow F n => a j) '' tsupport Φfin) :=
      isCompact_iUnion fun j => hcs.isCompact.image (continuous_apply j)
    obtain ⟨d, hd, hdK⟩ := exists_integer_mul_mem_of_isCompact F hK
    obtain ⟨B, hB⟩ := hfc.bounded_above_of_compact_support hcs
    refine ⟨d, hd, fun x hx j => ?_, fun N => ?_⟩
    · have hx' : Φfin (finiteCoordinates F n x) ≠ 0 := right_ne_zero_of_mul hx
      exact hdK _ (Set.mem_iUnion.mpr ⟨j, _, subset_tsupport _ hx', rfl⟩)
    · obtain ⟨C, hC⟩ := SchwartzMap.exists_one_add_pow_mul_le Φinf N
      refine ⟨C * max B 0, fun x => ?_⟩
      rw [norm_mul, ← mul_assoc]
      exact mul_le_mul (hC _) ((hB _).trans (le_max_left _ _)) (norm_nonneg _)
        ((le_trans (by positivity) (hC (archimedeanCoordinates F n x))))

/-- Schwartz–Bruhat functions are continuous, integrable and dominated. -/
theorem schwartzBruhat_properties (n : ℕ) [CompactSpace (AdeleQuotient F)]
    {Φ : RowVector F n → ℂ} (hΦ : Φ ∈ schwartzBruhat F n) :
    Continuous Φ ∧ Integrable Φ (rectangleMeasure F 1 n) ∧ IsRowDominated F n Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h => exact isPureSchwartzBruhat_properties F n h
  | zero => exact ⟨continuous_const, integrable_zero _ _ _, isRowDominated_zero n⟩
  | add Φ Ψ _ _ hΦ hΨ =>
    exact ⟨hΦ.1.add hΨ.1, hΦ.2.1.add hΨ.2.1, hΦ.2.2.add hΨ.2.2⟩
  | smul c Φ _ hΦ =>
    exact ⟨hΦ.1.const_smul c, hΦ.2.1.smul c, hΦ.2.2.smul c⟩

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
