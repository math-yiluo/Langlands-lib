import Langlands.Automorphic.CuspidalUnitaryForm

/-!
# Shifting the determinant band by central elements

For a realization with unitary central character, the squared norm of a realized function
has the same integral over every determinant band `α < |det| < 2α` of the quotient. A
closed band `[3/4, 9/4]` is covered by two such bands.
-/

noncomputable section

universe uF

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global NumberField

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance bandShiftIsAffine : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance bandShiftSmooth : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The open determinant band `α < |det| < 2α` of the quotient. -/
def bandAt (α : ℝ≥0) : Set (Quotient F n) :=
  {q | α < (quotientDeterminantNorm F n q : ℝ≥0) ∧ (quotientDeterminantNorm F n q : ℝ≥0) < 2 * α}

theorem isOpen_bandAt (α : ℝ≥0) : IsOpen (bandAt F n α) :=
  isOpen_Ioo.preimage (Units.continuous_val.comp (quotientDeterminantNorm F n).continuous)

theorem measurableSet_bandAt (α : ℝ≥0) : MeasurableSet (bandAt F n α) :=
  (isOpen_bandAt F n α).measurableSet

theorem bandAt_one : bandAt F n 1 = band F n := by
  ext q
  simp [bandAt, band]

/-- Right translation multiplies the quotient determinant norm. -/
theorem quotientDeterminantNorm_translate (g : AdelicGL F n) (q : Quotient F n) :
    quotientDeterminantNorm F n (translate F n g q) =
      quotientDeterminantNorm F n q * AdelicBlockDeterminantCharacter.determinantNorm F n g := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  rw [translate_point, quotientDeterminantNorm_point, quotientDeterminantNorm_point, map_mul]

theorem preimage_bandAt_translate (g : AdelicGL F n) {α : ℝ≥0ˣ}
    (hg : AdelicBlockDeterminantCharacter.determinantNorm F n g = α) :
    translate F n g ⁻¹' bandAt F n (α : ℝ≥0) = band F n := by
  ext q
  have hα : (0 : ℝ≥0) < α := pos_iff_ne_zero.mpr α.ne_zero
  simp only [Set.mem_preimage, bandAt, band, Set.mem_ofPred_eq,
    quotientDeterminantNorm_translate, hg, Units.val_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_right h hα.le
      rw [one_mul] at this
      exact absurd h1 (not_lt.mpr this)
    · by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_right h hα.le
      exact absurd h2 (not_lt.mpr this)
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa using mul_lt_mul_of_pos_right h1 hα,
      mul_lt_mul_of_pos_right h2 hα⟩

local instance bandShiftRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance bandShiftContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance bandShiftSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance bandShiftFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance bandShiftStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance bandShiftSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Translation by a central scalar does not change the norm of a realized function. -/
theorem enorm_toQuotient_translate_scalar (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ) (z : Ideles F) (f : S.Space)
    (q : Quotient F n) :
    ‖toQuotient F n S f (translate F n (AdelicGL.scalar F n z) q)‖ₑ =
      ‖toQuotient F n S f q‖ₑ := by
  have h := toQuotient_central F n S χ hS z f 1 q
  rw [mul_one, translate_one] at h
  rw [h, enorm_mul]
  have h1 : ‖((centralIdeleCharacter F χ z : ℂˣ) : ℂ)‖ₑ = 1 := by
    rw [← ofReal_norm]
    have : ‖((centralIdeleCharacter F χ z : ℂˣ) : ℂ)‖ = 1 := hχ _
    rw [this, ENNReal.ofReal_one]
  rw [h1, one_mul]

/-- **Band shift.** With a unitary central character, the squared norm of a realized
function has the same integral over every band `α < |det| < 2α`. -/
theorem lintegral_bandAt (hn : n ≠ 0) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ) (α : ℝ≥0ˣ) (f : S.Space) :
    ∫⁻ q in bandAt F n (α : ℝ≥0), ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n =
      ∫⁻ q in band F n, ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n := by
  obtain ⟨z, hz⟩ := exists_scalar_determinantNorm F n hn α
  have hmp := measurePreserving_translate F n (AdelicGL.scalar F n z)
  have hpre := preimage_bandAt_translate F n (AdelicGL.scalar F n z) hz
  rw [← hmp.setLIntegral_comp_preimage (measurableSet_bandAt F n _)
    ((toQuotient F n S f).continuous.measurable.enorm.pow_const 2), hpre]
  refine setLIntegral_congr_fun (measurableSet_band F n) fun q _ => ?_
  rw [enorm_toQuotient_translate_scalar F n S χ hχ hS z f q]

/-- The closed band `3/4 ≤ |det| ≤ 9/4` costs at most twice the band integral. -/
theorem lintegral_wideBand_le (hn : n ≠ 0) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ) (f : S.Space) :
    ∫⁻ q in {q : Quotient F n | (3 / 4 : ℝ≥0) ≤ (quotientDeterminantNorm F n q : ℝ≥0) ∧
        (quotientDeterminantNorm F n q : ℝ≥0) ≤ 9 / 4},
        ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n ≤
      2 * ∫⁻ q in band F n, ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n := by
  have h7 : (7 / 10 : ℝ≥0) ≠ 0 := by norm_num
  have h12 : (6 / 5 : ℝ≥0) ≠ 0 := by norm_num
  have hsub : {q : Quotient F n | (3 / 4 : ℝ≥0) ≤ (quotientDeterminantNorm F n q : ℝ≥0) ∧
      (quotientDeterminantNorm F n q : ℝ≥0) ≤ 9 / 4} ⊆
      bandAt F n ((Units.mk0 (7 / 10) h7 : ℝ≥0ˣ) : ℝ≥0) ∪
        bandAt F n ((Units.mk0 (6 / 5) h12 : ℝ≥0ˣ) : ℝ≥0) := by
    rintro q ⟨h1, h2⟩
    simp only [bandAt, Units.val_mk0, Set.mem_union, Set.mem_ofPred_eq]
    by_cases h : (quotientDeterminantNorm F n q : ℝ≥0) < 7 / 5
    · left
      refine ⟨lt_of_lt_of_le (by norm_num) h1, ?_⟩
      calc (quotientDeterminantNorm F n q : ℝ≥0) < 7 / 5 := h
        _ = 2 * (7 / 10) := by norm_num
    · right
      push Not at h
      refine ⟨lt_of_lt_of_le (by norm_num) h, ?_⟩
      calc (quotientDeterminantNorm F n q : ℝ≥0) ≤ 9 / 4 := h2
        _ < 2 * (6 / 5) := by norm_num
  calc _ ≤ ∫⁻ q in bandAt F n ((Units.mk0 (7 / 10) h7 : ℝ≥0ˣ) : ℝ≥0) ∪
          bandAt F n ((Units.mk0 (6 / 5) h12 : ℝ≥0ˣ) : ℝ≥0),
          ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n :=
        lintegral_mono_set hsub
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by
        rw [lintegral_bandAt F n S hn χ hχ hS, lintegral_bandAt F n S hn χ hχ hS, two_mul]

/-- **Closed bands.** For `0 < m`, the closed band `m ≤ |det| ≤ M` is covered by finitely many
open bands of ratio two, so its squared-norm integral is at most a fixed multiple of the band
integral. -/
theorem exists_lintegral_closedBand_le (hn : n ≠ 0) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ) {m M : ℝ≥0} (hm : 0 < m) :
    ∃ N : ℕ, ∀ f : S.Space,
      ∫⁻ q in {q : Quotient F n | m ≤ (quotientDeterminantNorm F n q : ℝ≥0) ∧
          (quotientDeterminantNorm F n q : ℝ≥0) ≤ M},
          ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n ≤
        N * ∫⁻ q in band F n, ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n := by
  have hK : IsCompact (Set.Icc m M) := isCompact_Icc
  have hpos : ∀ x : Set.Icc m M, (0 : ℝ≥0) < x := fun x => lt_of_lt_of_le hm x.2.1
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : Set.Icc m M => Set.Ioo (2 / 3 * (x : ℝ≥0)) (4 / 3 * (x : ℝ≥0)))
    (fun x => isOpen_Ioo) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by
      have := hpos ⟨y, hy⟩
      constructor
      · change 2 / 3 * y < y
        calc 2 / 3 * y < 1 * y := by gcongr; norm_num
          _ = y := one_mul y
      · change y < 4 / 3 * y
        calc y = 1 * y := (one_mul y).symm
          _ < 4 / 3 * y := by gcongr; norm_num⟩)
  have hα : ∀ x : Set.Icc m M, (2 / 3 * (x : ℝ≥0)) ≠ 0 := fun x =>
    (mul_pos (by norm_num) (hpos x)).ne'
  refine ⟨s.card, fun f => ?_⟩
  set H : Quotient F n → ℝ≥0∞ := fun q => ‖toQuotient F n S f q‖ₑ ^ 2
  have hsub : {q : Quotient F n | m ≤ (quotientDeterminantNorm F n q : ℝ≥0) ∧
      (quotientDeterminantNorm F n q : ℝ≥0) ≤ M} ⊆
      ⋃ x : s, bandAt F n ((Units.mk0 _ (hα x.1) : ℝ≥0ˣ) : ℝ≥0) := by
    intro q hq
    obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.mp (hs (show (quotientDeterminantNorm F n q : ℝ≥0) ∈
      Set.Icc m M from hq))
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    simp only [bandAt, Units.val_mk0, Set.mem_ofPred_eq]
    refine ⟨hqx.1, ?_⟩
    calc (quotientDeterminantNorm F n q : ℝ≥0) < 4 / 3 * (x : ℝ≥0) := hqx.2
      _ = 2 * (2 / 3 * (x : ℝ≥0)) := by ring
  calc ∫⁻ q in {q : Quotient F n | m ≤ (quotientDeterminantNorm F n q : ℝ≥0) ∧
        (quotientDeterminantNorm F n q : ℝ≥0) ≤ M}, H q ∂quotientHaarMeasure F n
      ≤ ∫⁻ q in ⋃ x : s, bandAt F n ((Units.mk0 _ (hα x.1) : ℝ≥0ˣ) : ℝ≥0), H q
          ∂quotientHaarMeasure F n := lintegral_mono_set hsub
    _ ≤ ∑' x : s, ∫⁻ q in bandAt F n ((Units.mk0 _ (hα x.1) : ℝ≥0ˣ) : ℝ≥0), H q
          ∂quotientHaarMeasure F n := lintegral_iUnion_le _ _
    _ = ∑' _x : s, ∫⁻ q in band F n, H q ∂quotientHaarMeasure F n := by
        congr 1
        funext x
        exact lintegral_bandAt F n S hn χ hχ hS _ f
    _ = s.card * ∫⁻ q in band F n, H q ∂quotientHaarMeasure F n := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
