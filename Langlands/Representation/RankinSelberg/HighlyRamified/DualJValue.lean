import Langlands.Representation.RankinSelberg.HighlyRamified.DualTarget
import Langlands.Representation.RankinSelberg.HighlyRamified.DualAverage
import Langlands.Representation.RankinSelberg.HighlyRamified.QuotientSupport
import Langlands.Representation.RankinSelberg.UnipotentQuotient

/-!
# The value of the reduced dual integral when the average is the target

On `N_(m+1) \ GL_(m+1)` with the canonical quotient measure: if `Ξ` transforms under `K⁰(f)` by
`ω(k₀₀)⁻¹` and under `N` by `ψ_N⁻¹`, and the `K⁰(f)`-average of `F` with weight `ω(k₀₀)⁻¹`
equals `c` times the target, then `∫ Ξ F = c Ξ(1)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis QuotientIntegration GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualJFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualJValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualJLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualJGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance dualJGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualJUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance dualJUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualJQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance dualJQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩

variable {m : ℕ} {ω : F.Carrierˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)

namespace LastRowReductionLocal

/-- Right invariance under an open subgroup gives continuity. -/
theorem continuous_of_rightInvariant {G Y : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace Y] (J : OpenSubgroup G) (φ : G → Y)
    (hφ : ∀ x, ∀ j ∈ J, φ (x * j) = φ x) : Continuous φ := by
  rw [continuous_iff_continuousAt]
  intro x
  have hn : (x * ·) '' (J : Set G) ∈ nhds x :=
    ((isOpenMap_mul_left x) _ J.isOpen).mem_nhds ⟨1, one_mem J, mul_one x⟩
  refine (continuousAt_const : ContinuousAt (fun _ : G => φ x) x).congr ?_
  filter_upwards [hn]
  rintro _ ⟨j, hj, rfl⟩
  exact (hφ x j hj).symm

end LastRowReductionLocal

/-- Right invariance under an open subgroup gives local constancy. -/
theorem isLocallyConstant_of_rightInvariant {G Y : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (L : OpenSubgroup G) (φ : G → Y)
    (hφ : ∀ g l, l ∈ L → φ (g * l) = φ g) : IsLocallyConstant φ := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (L : Set G),
    L.isOpen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro x hx
  have hx' : g⁻¹ * x ∈ L := hx
  calc φ x = φ (g * (g⁻¹ * x)) := by group
    _ = φ g := hφ _ _ hx'

theorem firstColumnWeight_isLocallyConstant (hω : TrivialOnPrincipalUnits ω f) :
    IsLocallyConstant (firstColumnWeight (m := m) ω hf) :=
  isLocallyConstant_of_rightInvariant (Conductor.principalLevelOpenSubgroup F.Carrier m f) _
    (fun g l hl => firstColumnWeight_mul_principal hf hω g l hl)

theorem firstColumnWeight_hasCompactSupport :
    HasCompactSupport (firstColumnWeight (m := m) ω hf) :=
  HasCompactSupport.intro (isCompact_firstColumnOpenSubgroup F.Carrier m f) fun _ hg =>
    firstColumnWeight_of_not_mem ω hf hg

/-- The integral unipotents are exactly the unipotents in `K⁰(f)`. -/
theorem unipotentHaar_firstColumn :
    unipotentHaar F.Carrier m {u : upperUnipotent (m + 1) F.Carrier |
      u.val ∈ (firstColumnOpenSubgroup F.Carrier m f :
        Set (GeneralLinear (m + 1) F.Carrier))} = 1 := by
  have hset : {u : upperUnipotent (m + 1) F.Carrier |
      u.val ∈ (firstColumnOpenSubgroup F.Carrier m f :
        Set (GeneralLinear (m + 1) F.Carrier))} =
      (unipotentIntegralOpen F.Carrier m : Set (upperUnipotent (m + 1) F.Carrier)) := by
    ext u
    change u.val ∈ firstColumnCongruence _ m _ ↔
      u.val ∈ Conductor.levelSubgroup F.Carrier m 0
    rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup,
      mem_firstColumnCongruence]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, fun j hj => ⟨0, Submodule.zero_mem _, ?_⟩⟩
      have : (u.val : Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier) j 0 = 0 :=
        u.property.1 (show id (0 : Fin (m + 1)) < id j from Fin.pos_of_ne_zero hj)
      rw [this]
      rfl
  rw [hset, unipotentHaar_integral]

/-- If the weighted `K⁰(f)`-average of `F` is `c` times the target, then `∫ Ξ F = c Ξ(1)`. -/
theorem dual_pairing_of_average_eq_target (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F.Carrier →* ℂˣ)
    (hψN : ∀ n : upperUnipotent (m + 1) F.Carrier,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F.Carrier).integer) → ψN n = 1)
    (Ξ Fn : GeneralLinear (m + 1) F.Carrier → ℂ)
    (LΞ LF : OpenSubgroup (GeneralLinear (m + 1) F.Carrier))
    (hΞL : ∀ g l, l ∈ LΞ → Ξ (g * l) = Ξ g) (hFL : ∀ g l, l ∈ LF → Fn (g * l) = Fn g)
    (hΞK : ∀ g k (hk : InFirstColumn f k),
      Ξ (g * k) = ((ω (firstEntryUnit hf k hk) : ℂ))⁻¹ * Ξ g)
    (hΞN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, Ξ (u.val * g) = ((ψN u : ℂ))⁻¹ * Ξ g)
    (hFN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, Fn (u.val * g) = (ψN u : ℂ) * Fn g)
    (hint : Integrable (fun q : LeftQuotient (upperUnipotent (m + 1) F.Carrier) =>
      Ξ q.out * Fn q.out) (unipotentQuotientHaar F.Carrier m))
    (c : ℂ)
    (havg : ∀ g, rightAverage (generalLinearHaar F.Carrier m) Fn LF hFL (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω) (firstColumnWeight_hasCompactSupport F hf) g =
      c * firstColumnTarget ω hf ψN g) :
    ∫ q, Ξ q.out * Fn q.out ∂unipotentQuotientHaar F.Carrier m = c * Ξ 1 := by
  have hcompat := unipotentQuotientHaar_isCompatible F.Carrier m
  set K := firstColumnOpenSubgroup F.Carrier m f with hK
  set μG := generalLinearHaar F.Carrier m with hμG
  have hKm : MeasurableSet (K : Set (GeneralLinear (m + 1) F.Carrier)) := K.isOpen.measurableSet
  have hKpos : 0 < μG (K : Set (GeneralLinear (m + 1) F.Carrier)) :=
    K.isOpen.measure_pos μG ⟨1, K.one_mem⟩
  have hKfin : μG (K : Set (GeneralLinear (m + 1) F.Carrier)) < ⊤ :=
    (isCompact_firstColumnOpenSubgroup F.Carrier m f).measure_lt_top
  set V : ℝ := μG.real (K : Set (GeneralLinear (m + 1) F.Carrier)) with hV
  have hVne : (V : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, hV, measureReal_def]
    exact (ENNReal.toReal_pos hKpos.ne' hKfin.ne).ne'
  -- the averaging identity
  have hpair := integral_pair_rightAverage (unipotentQuotientHaar F.Carrier m)
    hcompat.right_invariant μG Fn LF hFL (firstColumnWeight ω hf)
    (firstColumnWeight_isLocallyConstant F hf hω) (firstColumnWeight_hasCompactSupport F hf)
    Ξ (firstColumnCharacter ω hf)
    (fun g k hk => by
      have hk' := firstColumnWeight_ne_zero ω hf hk
      rw [hΞK g k hk', firstColumnCharacter_of_mem ω hf hk'])
    (fun k hk => by
      have hk' := firstColumnWeight_ne_zero ω hf hk
      rw [firstColumnCharacter_of_mem ω hf hk']
      simp)
    (fun u g => by
      rw [hΞN, hFN]
      field_simp)
    hint
  have hwb : ∫ k, firstColumnWeight ω hf k * (firstColumnCharacter ω hf k)⁻¹ ∂μG = V := by
    simp_rw [firstColumnWeight_mul_inv]
    change ∫ k, (K : Set (GeneralLinear (m + 1) F.Carrier)).indicator (fun _ => (1 : ℂ)) k ∂μG = V
    rw [integral_indicator_const _ hKm]
    simp [hV]
  rw [hwb] at hpair
  -- the averaged pairing via the target
  have htarget : ∫ q, Ξ q.out * firstColumnTarget ω hf ψN q.out ∂unipotentQuotientHaar F.Carrier m =
      Ξ 1 * V := by
    have hφc : Continuous (fun g => Ξ g * firstColumnTarget ω hf ψN g) := by
      apply LastRowReductionLocal.continuous_of_rightInvariant
        (LΞ ⊓ Conductor.principalLevelOpenSubgroup F.Carrier m f)
      intro g l hl
      rw [hΞL g l hl.1, firstColumnTarget_mul_principal hf hω ψN hψN g l hl.2]
    rw [integral_out_of_support (upperUnipotent (m + 1) F.Carrier) μG
      (unipotentHaar F.Carrier m) _ hcompat K (isCompact_firstColumnOpenSubgroup F.Carrier m f)
      (unipotentHaar_firstColumn F) _ hφc
      (fun u g => by
        rw [hΞN, firstColumnTarget_unipotent_mul hf hω ψN hψN]
        field_simp)
      (fun g hg => by
        have ht : firstColumnTarget ω hf ψN g ≠ 0 := right_ne_zero_of_mul hg
        obtain ⟨u, hu⟩ := firstColumnTarget_support hf ψN ht
        exact ⟨u, hu⟩)]
    have hind : (K : Set (GeneralLinear (m + 1) F.Carrier)).indicator
        (fun g => Ξ g * firstColumnTarget ω hf ψN g) =
        (K : Set (GeneralLinear (m + 1) F.Carrier)).indicator (fun _ => Ξ 1) := by
      funext k
      by_cases hk : k ∈ (K : Set (GeneralLinear (m + 1) F.Carrier))
      · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
        have hk' : InFirstColumn f k := hk
        have h1 := hΞK 1 k hk'
        have h2 := firstColumnTarget_mul hf hω ψN hψN 1 hk'
        simp only [one_mul, OneMemClass.coe_one, map_one, Units.val_one] at h1 h2
        rw [h1, h2]
        field_simp
      · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]
    rw [hind, integral_indicator_const _ hKm]
    simp [hV, mul_comm]
  have hleft : ∫ q, Ξ q.out * rightAverage μG Fn LF hFL (firstColumnWeight ω hf)
      (firstColumnWeight_isLocallyConstant F hf hω) (firstColumnWeight_hasCompactSupport F hf)
        q.out ∂unipotentQuotientHaar F.Carrier m = c * (Ξ 1 * V) := by
    simp_rw [havg]
    rw [← htarget, ← integral_const_mul]
    congr 1
    funext q
    ring
  rw [hleft] at hpair
  have : (V : ℂ) * ∫ q, Ξ q.out * Fn q.out ∂unipotentQuotientHaar F.Carrier m =
      (V : ℂ) * (c * Ξ 1) := by
    rw [← hpair]; ring
  exact mul_left_cancel₀ hVne this

end Langlands.RankinSelberg.HighlyRamified
