import Langlands.Representation.GodementJacquet.LocalTateUnits
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # The unit Haar comparison and unit integrals of characters -/

noncomputable section

namespace Langlands.GodementJacquet.LocalTate

open MeasureTheory HarmonicAnalysis Topology ValuativeRel Conductor RankinSelberg
open GeneralLinear.Iwasawa
open scoped ENNReal NNReal

universe uF

/-- The pullback of a measure along a measurable embedding of a group, whose image
translations preserve the measure, is left invariant. -/
theorem isMulLeftInvariant_comap_of_preimage {G M : Type*} [Group G] [Monoid M]
    [MeasurableSpace G] [MeasurableSpace M] [MeasurableMul G] (e : G →* M)
    (he : MeasurableEmbedding e) (ν : Measure M)
    (hν : ∀ (g : G) (A : Set M), MeasurableSet A → ν ((fun x => e g * x) ⁻¹' A) = ν A) :
    (ν.comap e).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, he.comap_apply, he.comap_apply]
    have himage : e '' ((fun x => g * x) ⁻¹' s) = (fun x => e g * x) ⁻¹' (e '' s) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨g * k, hk, map_mul e g k⟩
      · rintro ⟨k, hk, hx⟩
        refine ⟨g⁻¹ * k, by simpa using hk, ?_⟩
        rw [map_mul, hx, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    rw [himage, hν g _ (he.measurableSet_image.mpr hs)]

/-- The unit sphere `{x | v x = 1}` of a valued field. -/
def unitShell (F : Type uF) [Field F] [ValuativeRel F] : Set F := {x | valuation F x = 1}

/-- A function on the units, extended by zero to the field. -/
def extendUnits {F : Type uF} [Field F] (f : Fˣ → ℂ) (x : F) : ℂ := by
  classical
  exact if h : x = 0 then 0 else f (Units.mk0 x h)

@[simp] theorem extendUnits_val {F : Type uF} [Field F] (f : Fˣ → ℂ) (u : Fˣ) :
    extendUnits f (u : F) = f u := by
  simp [extendUnits, u.ne_zero]

theorem extendUnits_of_ne_zero {F : Type uF} [Field F] (f : Fˣ → ℂ) {x : F} (hx : x ≠ 0) :
    extendUnits f x = f (Units.mk0 x hx) := by
  simp [extendUnits, hx]

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] (N : Normalization F)

theorem unitShell_eq : unitShell F = (N.ball 0 : Set F) \ N.ball 1 := by
  ext x
  by_cases hx : x = 0
  · subst hx
    simp [unitShell]
  · simp only [unitShell, Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe,
      N.mem_ball_iff_ord hx, ← N.ord_eq_zero_iff hx]
    omega

/-- The values of the integral units in the field form the unit shell. -/
theorem range_integralUnits_val :
    Set.range (fun k : integralUnits (valuation F).integer => ((k : Fˣ) : F)) =
      unitShell F := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact mem_integralUnits_iff.mp k.2
  · intro hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp [unitShell] at hx
    exact ⟨⟨Units.mk0 x hx0, mem_integralUnits_iff.mpr hx⟩, rfl⟩

/-- Adding an element of `ϖ ^ n O`, `n ≥ 1`, preserves the unit shell. -/
theorem add_mem_unitShell_iff {n : ℤ} (hn : 1 ≤ n) {t : F} (ht : t ∈ N.ball n) (x : F) :
    x + t ∈ unitShell F ↔ x ∈ unitShell F := by
  have ht' : t ∈ N.ball 1 := N.ball_antitone hn ht
  rw [N.unitShell_eq, Set.mem_sdiff, Set.mem_sdiff]
  simp only [SetLike.mem_coe]
  rw [(N.ball 1).add_mem_cancel_right ht',
    (N.ball 0).add_mem_cancel_right (N.ball_antitone (by norm_num) ht')]

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

include N

theorem isOpen_unitShell : IsOpen (unitShell F) := by
  rw [N.unitShell_eq]
  exact (N.isOpen_ball 0).sdiff (N.isClosed_ball 1)

omit N in
theorem isCompact_integralUnits :
    IsCompact (integralUnits (valuation F).integer : Set Fˣ) := by
  have := localField_t2 F
  exact integralUnits_isCompact _

omit N in
theorem isOpen_integralUnits : IsOpen (integralUnits (valuation F).integer : Set Fˣ) :=
  integralUnits_isOpen _ Valuation.isOpen_integer

theorem isOpen_unitLevel (m : ℕ) : IsOpen (N.unitLevel m : Set Fˣ) := by
  have h : (N.unitLevel m : Set Fˣ) = (integralUnits (valuation F).integer : Set Fˣ) ∩
      Units.val ⁻¹' {x : F | x - 1 ∈ N.ball m} := by
    ext u
    simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_integralUnits_iff, Set.mem_preimage,
      Set.mem_ofPred_eq]
    rfl
  rw [h]
  exact isOpen_integralUnits.inter
    (((N.isOpen_ball m).preimage (continuous_id.sub continuous_const)).preimage
      Units.continuous_val)

section Measure

variable [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

theorem measurableSet_unitShell : MeasurableSet (unitShell F) :=
  N.isOpen_unitShell.measurableSet

omit [BorelSpace F] in
theorem measure_unitShell_pos : 0 < ν (unitShell F) :=
  N.isOpen_unitShell.measure_pos ν ⟨1, by simp [unitShell]⟩

theorem measure_unitShell_lt_top : ν (unitShell F) < ∞ := by
  rw [N.unitShell_eq]
  exact (measure_mono Set.sdiff_subset).trans_lt (N.measure_ball_lt_top ν 0)

theorem measure_unitShell :
    (ν (unitShell F)).toReal = (ν (N.ball 0)).toReal - (ν (N.ball 1)).toReal := by
  rw [N.unitShell_eq, measure_sdiff (N.ball_antitone (by norm_num))
    (N.measurableSet_ball 1).nullMeasurableSet (N.measure_ball_lt_top ν 1).ne,
    ENNReal.toReal_sub_of_le (measure_mono (N.ball_antitone (by norm_num)))
      (N.measure_ball_lt_top ν 0).ne]

theorem measure_unitShell_toReal_pos : 0 < (ν (unitShell F)).toReal :=
  ENNReal.toReal_pos (N.measure_unitShell_pos ν).ne' (N.measure_unitShell_lt_top ν).ne

variable [MeasurableSpace Fˣ] [BorelSpace Fˣ]

/-- **Haar comparison on the integral units.** The normalized multiplicative Haar
integral over `O^×` is the additive Haar integral over the unit shell divided by
the additive mass of the shell. -/
theorem setIntegral_integralUnits (g : F → ℂ) :
    ∫ u in (integralUnits (valuation F).integer : Set Fˣ), g (u : F)
        ∂localMultiplicativeHaar F =
      ((ν (unitShell F)).toReal : ℂ)⁻¹ * ∫ x in unitShell F, g x ∂ν := by
  have := localField_t2 F
  set U := integralUnits (valuation F).integer with hUdef
  have hUo : IsOpen (U : Set Fˣ) := isOpen_integralUnits
  have hUm : MeasurableSet (U : Set Fˣ) := hUo.measurableSet
  have : CompactSpace U := isCompact_iff_compactSpace.mp isCompact_integralUnits
  let e : U →* F := (Units.coeHom F).comp U.subtype
  have heU : MeasurableEmbedding (Subtype.val : U → Fˣ) := MeasurableEmbedding.subtype_coe hUm
  have he : MeasurableEmbedding e :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := F)).measurableEmbedding.comp heU
  have hrange : Set.range e = unitShell F := range_integralUnits_val
  have hrangeU : Set.range (Subtype.val : U → Fˣ) = (U : Set Fˣ) := by
    ext u
    simp
  set lK : Measure U := (localMultiplicativeHaar F).comap Subtype.val with hlK
  have : lK.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (localMultiplicativeHaar F) (f := U.subtype)
      (mH := inferInstance) hUo.isOpenEmbedding_subtypeVal
  set νK : Measure U := ν.comap e with hνK
  have : νK.IsMulLeftInvariant := by
    refine isMulLeftInvariant_comap_of_preimage e he ν fun k A hA => ?_
    have hscale := HarmonicAnalysis.generalScalarHaarScalingStatement F N.q N.hq N.abv N.ϖ
      N.hϖ N.habvϖ N.habv1 ν (k : Fˣ)
    have h := congrArg (fun μ : Measure F => μ A) hscale
    rw [Measure.map_apply (measurable_const_mul _) hA, Measure.smul_apply] at h
    have habs : ((Shahidi.absUnits N.abv (k : Fˣ) : ℝ≥0ˣ) : ℝ≥0) = 1 := by
      apply NNReal.eq
      rw [Shahidi.absUnits_apply, NNReal.coe_one]
      exact N.habv1 _ (mem_integralUnits_iff.mp k.2)
    rw [habs, inv_one, one_smul] at h
    exact h
  have : IsFiniteMeasure νK := ⟨by
    rw [he.comap_apply, Set.image_univ, hrange]
    exact N.measure_unitShell_lt_top ν⟩
  have hfac := Measure.isMulInvariant_eq_smul_of_compactSpace νK lK
  set c := Measure.haarScalarFactor νK lK with hcdef
  have hlKuniv : lK Set.univ = 1 := by
    rw [hlK, heU.comap_apply, Set.image_univ, hrangeU]
    exact localMultiplicativeHaar_integerUnits F
  have hc : (c : ℝ≥0∞) = ν (unitShell F) := by
    have h := congrArg (fun m : Measure U => m Set.univ) hfac
    rw [Measure.smul_apply, hlKuniv, hνK, he.comap_apply, Set.image_univ, hrange] at h
    rw [h, ENNReal.smul_def, smul_eq_mul, mul_one]
  have hL : ∫ u in (U : Set Fˣ), g (u : F) ∂localMultiplicativeHaar F =
      ∫ k, g (e k) ∂lK := by
    rw [← hrangeU, ← heU.map_comap, heU.integral_map]
    rfl
  have hR : ∫ x in unitShell F, g x ∂ν = ∫ k, g (e k) ∂νK := by
    rw [← hrange, ← he.map_comap, he.integral_map]
  have hcR : (ν (unitShell F)).toReal = (c : ℝ) := by
    rw [← hc, ENNReal.coe_toReal]
  have hc0 : (c : ℂ) ≠ 0 := by
    have := N.measure_unitShell_toReal_pos ν
    rw [hcR] at this
    exact_mod_cast this.ne'
  rw [hL, hR, hfac, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hcR,
    inv_mul_cancel_left₀ hc0]

/-- The multiplicative mass of a positive unit level. -/
theorem measure_unitLevel {m : ℕ} (hm : 0 < m) :
    (localMultiplicativeHaar F (N.unitLevel m : Set Fˣ)).toReal =
      (ν (N.ball m)).toReal / (ν (unitShell F)).toReal := by
  set S : Set F := {x : F | x - 1 ∈ N.ball m}
  have hSm : MeasurableSet S :=
    ((N.isOpen_ball m).preimage (continuous_id.sub continuous_const)).measurableSet
  have hSsub : S ⊆ unitShell F := by
    intro x hx
    have h := (N.add_mem_unitShell_iff (n := m) (by exact_mod_cast hm) hx 1).mpr
      (by simp [unitShell])
    simpa using h
  have hSν : ν S = ν (N.ball m) := by
    have : S = (fun x => x + (-1 : F)) ⁻¹' (N.ball m : Set F) := by
      ext x
      simp [S, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
  have h := N.setIntegral_integralUnits ν (S.indicator 1)
  have hleft : ∀ u : Fˣ, S.indicator (1 : F → ℂ) (u : F) =
      (N.unitLevel m : Set Fˣ).indicator 1 u := by
    intro u
    by_cases hu : u ∈ N.unitLevel m
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem
        (show (u : F) ∈ S from (N.mem_unitLevel_iff_of_pos hm).mp hu)]
      rfl
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem
        (show (u : F) ∉ S from fun h => hu ((N.mem_unitLevel_iff_of_pos hm).mpr h))]
  simp_rw [hleft] at h
  rw [setIntegral_indicator (N.isOpen_unitLevel m).measurableSet,
    setIntegral_indicator hSm, Set.inter_eq_right.mpr (N.unitLevel_le_integralUnits m),
    Set.inter_eq_right.mpr hSsub] at h
  simp only [Pi.one_apply, setIntegral_const, Measure.real, Complex.real_smul, mul_one] at h
  rw [hSν] at h
  have h' : ((localMultiplicativeHaar F (N.unitLevel m : Set Fˣ)).toReal : ℂ) =
      (((ν (N.ball m)).toReal / (ν (unitShell F)).toReal : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast h'

end Measure

section Characters

variable [MeasurableSpace Fˣ] [BorelSpace Fˣ]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace Fˣ] [BorelSpace Fˣ] in
/-- A character trivial on `1 + ϖ ^ n O`, `n ≥ 1`, is invariant on the unit shell under
translation by `ϖ ^ n O`. -/
theorem extendUnits_add_of_mem_ball {η : Fˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n)
    (hη : ∀ u ∈ N.unitLevel n, η u = 1) {x t : F} (hx : x ∈ unitShell F) (ht : t ∈ N.ball n) :
    extendUnits (fun u => (η u : ℂ)) (x + t) = extendUnits (fun u => (η u : ℂ)) x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [unitShell] at hx
  have hxt : x + t ≠ 0 := by
    intro h
    have := (N.add_mem_unitShell_iff (n := n) (by exact_mod_cast hn) ht x).mpr hx
    rw [h] at this
    simp [unitShell] at this
  set w : Fˣ := Units.mk0 (x + t) hxt * (Units.mk0 x hx0)⁻¹ with hw
  have hwval : (w : F) - 1 = t * x⁻¹ := by
    simp only [hw, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    ring
  have hwmem : w ∈ N.unitLevel n := by
    rw [N.mem_unitLevel_iff_of_pos (by omega), hwval]
    have hxinv : x⁻¹ ∈ N.ball 0 := by
      rw [mem_ball, map_inv₀, show valuation F x = 1 from hx, inv_one, zpow_zero]
    simpa using N.mul_mem_ball ht hxinv
  have hmk : Units.mk0 (x + t) hxt = w * Units.mk0 x hx0 := by
    rw [hw, inv_mul_cancel_right]
  rw [extendUnits_of_ne_zero _ hxt, extendUnits_of_ne_zero _ hx0, hmk, map_mul, hη w hwmem,
    one_mul]

/-- The integral of a character of exact conductor `a` over the unit level `m`. -/
theorem setIntegral_unitLevel_char {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a)
    (m : ℕ) :
    ∫ u in (N.unitLevel m : Set Fˣ), (η u : ℂ) ∂localMultiplicativeHaar F =
      if a ≤ m then ((localMultiplicativeHaar F (N.unitLevel m : Set Fˣ)).toReal : ℂ)
      else 0 := by
  split_ifs with ham
  · have h1 : Set.EqOn (fun u => (η u : ℂ)) (fun _ => 1) (N.unitLevel m : Set Fˣ) := by
      intro u hu
      simp [hη.1 u (N.unitLevel_antitone ham hu)]
    rw [setIntegral_congr_fun (N.isOpen_unitLevel m).measurableSet h1, setIntegral_const]
    simp [Measure.real]
  · obtain ⟨w, hw, hne⟩ := hη.2 m (not_le.mp ham)
    refine setIntegral_eq_zero_of_mul_left _ (N.isOpen_unitLevel m).measurableSet (w := w)
      (fun x => (N.unitLevel m).mul_mem_cancel_left hw) (c := (η w : ℂ))
      (fun h => hne (Units.val_eq_one.mp h)) ?_
    intro x _
    simp [map_mul]

/-- The integral of a character of exact conductor `a` over `O^×`. -/
theorem setIntegral_integralUnits_char {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a) :
    ∫ u in (integralUnits (valuation F).integer : Set Fˣ), (η u : ℂ)
        ∂localMultiplicativeHaar F = if a = 0 then 1 else 0 := by
  have h := N.setIntegral_unitLevel_char hη 0
  rw [N.unitLevel_zero, localMultiplicativeHaar_integerUnits] at h
  rw [h]
  simp

omit N in
/-- The twisted Gauss integral `∫_{O^×} ψ(ϖ ^ k u) η(u) d^×u`. -/
def gaussIntegral (N : Normalization F) (ψ : UnitaryAdditiveCharacter F) (η : Fˣ →* ℂˣ)
    (k : ℤ) : ℂ :=
  ∫ u in (integralUnits (valuation F).integer : Set Fˣ),
    ψ.complex ((N.ϖ : F) ^ k * u) * (η u : ℂ) ∂localMultiplicativeHaar F

variable {ψ : UnitaryAdditiveCharacter F} (hψ : HasIntegerConductor ψ)
include hψ

/-- For `k ≥ 0` the Gauss integral is the unit integral of the character. -/
theorem gaussIntegral_of_nonneg {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a) {k : ℤ}
    (hk : 0 ≤ k) : N.gaussIntegral ψ η k = if a = 0 then 1 else 0 := by
  rw [gaussIntegral, ← N.setIntegral_integralUnits_char hη]
  refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
  have hu0 : (u : F) ∈ N.ball 0 := by
    rw [mem_ball, mem_integralUnits_iff.mp hu, zpow_zero]
  have hmem : (N.ϖ : F) ^ k * u ∈ N.ball 0 :=
    N.ball_antitone (by omega) (N.mul_mem_ball (N.ϖ_zpow_mem_ball k) hu0)
  rw [N.char_eq_one_of_mem_ball_zero hψ hmem, one_mul]

/-- For `-a < k < 0` the Gauss integral of a character of conductor `a` vanishes. -/
theorem gaussIntegral_eq_zero_of_neg {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a)
    {k : ℤ} (hk0 : k < 0) (hka : -(a : ℤ) < k) : N.gaussIntegral ψ η k = 0 := by
  set j : ℕ := (-k).toNat with hj
  have hjk : (j : ℤ) = -k := Int.toNat_of_nonneg (by omega)
  obtain ⟨w, hw, hne⟩ := hη.2 j (by omega)
  have hw0 : w ∈ integralUnits (valuation F).integer := N.unitLevel_le_integralUnits j hw
  refine setIntegral_eq_zero_of_mul_left _ isOpen_integralUnits.measurableSet (w := w)
    (fun x => (integralUnits (valuation F).integer).mul_mem_cancel_left hw0) (c := (η w : ℂ))
    (fun h => hne (Units.val_eq_one.mp h)) ?_
  intro x hx
  have hx0 : (x : F) ∈ N.ball 0 := by
    rw [mem_ball, mem_integralUnits_iff.mp hx, zpow_zero]
  have hsplit : (N.ϖ : F) ^ k * ((w * x : Fˣ) : F) =
      (N.ϖ : F) ^ k * x + (N.ϖ : F) ^ k * (((w : F) - 1) * x) := by
    push_cast
    ring
  have hmem : (N.ϖ : F) ^ k * (((w : F) - 1) * x) ∈ N.ball 0 := by
    have := N.mul_mem_ball (N.ϖ_zpow_mem_ball k) (N.mul_mem_ball hw.2 hx0)
    exact N.ball_antitone (by omega) this
  rw [hsplit, AddChar.map_add_eq_mul, N.char_eq_one_of_mem_ball_zero hψ hmem, mul_one,
    map_mul η w x, Units.val_mul]
  ring

variable [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

include ν in
/-- For `k < -max a 1` the Gauss integral of a character of conductor `a` vanishes. -/
theorem gaussIntegral_eq_zero_of_lt {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a)
    {k : ℤ} (hk : k < -(max a 1 : ℕ)) : N.gaussIntegral ψ η k = 0 := by
  set n : ℕ := max a 1 with hn
  have hn1 : 1 ≤ n := le_max_right a 1
  have hηn : ∀ u ∈ N.unitLevel n, η u = 1 := fun u hu =>
    hη.1 u (N.unitLevel_antitone (le_max_left a 1) hu)
  have hy : (N.ϖ : F) ^ k ∉ N.ball (-(n : ℤ)) := by
    intro h
    rw [N.mem_ball_iff_ord (zpow_ne_zero _ N.ϖ.ne_zero), N.ord_zpow_ϖ] at h
    omega
  obtain ⟨t, ht, hne⟩ := N.exists_char_ne_one hψ hy
  have h := N.setIntegral_integralUnits ν
    (fun x => ψ.complex ((N.ϖ : F) ^ k * x) * extendUnits (fun u => (η u : ℂ)) x)
  simp only [extendUnits_val] at h
  rw [gaussIntegral, h, setIntegral_eq_zero_of_add_right ν N.measurableSet_unitShell (t := t)
    (N.add_mem_unitShell_iff (by exact_mod_cast hn1) ht) hne, mul_zero]
  intro x hx
  rw [N.extendUnits_add_of_mem_ball hn1 hηn hx ht, mul_add, AddChar.map_add_eq_mul,
    mul_comm t]
  ring

/-- For an unramified character the Gauss integral at `k = -1` is
`-ν(ϖ O) / ν(O^×)`. -/
theorem gaussIntegral_neg_one {η : Fˣ →* ℂˣ} (hη : N.IsUnitConductor η 0) :
    N.gaussIntegral ψ η (-1) =
      -((ν (N.ball 1)).toReal : ℂ) / ((ν (unitShell F)).toReal : ℂ) := by
  have h1 : N.gaussIntegral ψ η (-1) = ∫ u in (integralUnits (valuation F).integer : Set Fˣ),
      ψ.complex ((N.ϖ : F) ^ (-1 : ℤ) * u) ∂localMultiplicativeHaar F := by
    refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
    have : η u = 1 := hη.1 u (by rwa [N.unitLevel_zero])
    simp [this]
  have := localField_t2 F
  have hint : IntegrableOn (fun x => ψ.complex (x * (N.ϖ : F) ^ (-1 : ℤ))) (N.ball 0 : Set F)
      ν :=
    (ψ.continuous_complex.comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact
      (N.isCompact_ball 0)
  have hnot : (N.ϖ : F) ^ (-1 : ℤ) ∉ N.ball (-0) := by
    intro h
    rw [neg_zero, N.mem_ball_iff_ord (zpow_ne_zero _ N.ϖ.ne_zero), N.ord_zpow_ϖ] at h
    omega
  have hin : (N.ϖ : F) ^ (-1 : ℤ) ∈ N.ball (-1) := N.ϖ_zpow_mem_ball (-1)
  have hshell : ∫ x in unitShell F, ψ.complex ((N.ϖ : F) ^ (-1 : ℤ) * x) ∂ν =
      -((ν (N.ball 1)).toReal : ℂ) := by
    simp_rw [mul_comm ((N.ϖ : F) ^ (-1 : ℤ))]
    rw [N.unitShell_eq, setIntegral_sdiff (N.measurableSet_ball 1) hint
      (N.ball_antitone (by norm_num)), N.integral_ball_char hψ ν 0, N.integral_ball_char hψ ν 1]
    simp only [hnot, hin, ↓reduceIte, zero_sub]
  rw [h1, N.setIntegral_integralUnits ν (fun x => ψ.complex ((N.ϖ : F) ^ (-1 : ℤ) * x)),
    hshell, div_eq_inv_mul, mul_neg]

end Characters

end LocalField

end Normalization

end Langlands.GodementJacquet.LocalTate
