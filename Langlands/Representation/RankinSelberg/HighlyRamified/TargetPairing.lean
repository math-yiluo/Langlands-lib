import Langlands.Representation.RankinSelberg.HighlyRamified.DualJValue

/-!
# Pairings with the target function

For the target `t(u k) = ψ_N(u) ω(k₀₀)` on `N K⁰(f)`:

* `t(g k) = t(g) ω(k₀₀)` for `k ∈ K⁰(f)`, so the weighted right average of `t` is
  `vol(K⁰(f)) t`;
* the quotient integral of `t W` is `∫_(K⁰(f)) ω(k₀₀) W(k) dk`;
* hence `∫_(K⁰(f)) ω(k₀₀) W_avg(k) dk = vol(K⁰(f)) ∫ t W` for the inverse average `W_avg`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis QuotientIntegration Matrix Langlands.GeneralLinear

universe uF

section Algebra

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

/-- `(k₁ k)₀₀ ≡ k₁₀₀ k₀₀` modulo `𝔭^f` for `k₁, k ∈ K⁰(f)`. -/
theorem firstEntry_mul_firstColumn {f : ℕ} {k₁ k : GeneralLinearGroup (Fin (m + 1)) F}
    (hk₁ : InFirstColumn f k₁) (hk : InFirstColumn f k) :
    ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (k₁ * k : GeneralLinearGroup (Fin (m + 1)) F) 0 0 = k₁ 0 0 * k 0 0 + y := by
  classical
  obtain ⟨hint₁, -, -⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ k₁).1 hk₁
  obtain ⟨-, -, hcol⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ k).1 hk
  have hcol' : ∀ j : Fin (m + 1), ∃ x : (ValuativeRel.valuation F).integer,
      x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (x : F) = if j = 0 then 0 else k j 0 := by
    intro j
    by_cases hj : j = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [hj]⟩
    · obtain ⟨x, hx, hxe⟩ := hcol j hj
      exact ⟨x, hx, by simp [hj, hxe]⟩
  choose x hx hxe using hcol'
  refine ⟨∑ j, ⟨_, hint₁ 0 j⟩ * x j, Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j),
    ?_⟩
  change ((k₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * k) 0 0 = _
  rw [Matrix.mul_apply]
  have hsplit : ∀ j, k₁ 0 j * k j 0 =
      k₁ 0 j * (if j = 0 then 0 else k j 0) + (if j = 0 then k₁ 0 0 * k 0 0 else 0) := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, hxe]
  ring

variable {ω : Fˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)

/-- `ω((k₁ k)₀₀) = ω(k₁₀₀) ω(k₀₀)` on `K⁰(f)`. -/
theorem omega_firstEntry_mul (hω : TrivialOnPrincipalUnits ω f)
    {k₁ k : GeneralLinearGroup (Fin (m + 1)) F} (hk₁ : InFirstColumn f k₁)
    (hk : InFirstColumn f k) (hkk : InFirstColumn f (k₁ * k)) :
    (ω (firstEntryUnit hf (k₁ * k) hkk) : ℂ) =
      (ω (firstEntryUnit hf k₁ hk₁) : ℂ) * ω (firstEntryUnit hf k hk) := by
  rw [← Units.val_mul, ← map_mul]
  congr 1
  apply omega_eq_of_sub_mem hω
  · rw [Units.val_inv_eq_inv_val, Units.val_mul, firstEntryUnit_val, firstEntryUnit_val, mul_inv]
    exact Subring.mul_mem _ (firstColumn_entry_isUnit hf hk₁).2.2
      (firstColumn_entry_isUnit hf hk).2.2
  · simpa using firstEntry_mul_firstColumn hk₁ hk

/-- Right `K⁰(f)`-equivariance of the target: `t(g k) = t(g) ω(k₀₀)`. -/
theorem firstColumnTarget_mul_firstColumn (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F →* ℂˣ)
    (hψN : ∀ n : upperUnipotent (m + 1) F,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F).integer) → ψN n = 1)
    (g : GeneralLinearGroup (Fin (m + 1)) F) {k : GeneralLinearGroup (Fin (m + 1)) F}
    (hk : InFirstColumn f k) :
    firstColumnTarget ω hf ψN (g * k) =
      firstColumnTarget ω hf ψN g * ω (firstEntryUnit hf k hk) := by
  by_cases h : ∃ u : upperUnipotent (m + 1) F, InFirstColumn f (u.val⁻¹ * g)
  · obtain ⟨u, hu⟩ := h
    have hg : g = u.val * (u.val⁻¹ * g) := by simp
    have hgk : InFirstColumn f (u.val⁻¹ * g * k) := mul_mem hu hk
    rw [hg, mul_assoc, firstColumnTarget_mul hf hω ψN hψN _ hgk,
      firstColumnTarget_mul hf hω ψN hψN _ hu, omega_firstEntry_mul hf hω hu hk hgk]
    ring
  · have h' : ¬ ∃ u : upperUnipotent (m + 1) F, InFirstColumn f (u.val⁻¹ * (g * k)) := by
      rintro ⟨u, hu⟩
      apply h
      exact ⟨u, by simpa [mul_assoc] using mul_mem hu (inv_mem hk)⟩
    rw [firstColumnTarget_of_not_mem hf ψN h, firstColumnTarget_of_not_mem hf ψN h', zero_mul]

end Algebra

section Measure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance targetPairingFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance targetPairingValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance targetPairingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance targetPairingGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance targetPairingGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance targetPairingUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance targetPairingUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance targetPairingQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance targetPairingQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩

variable {m : ℕ}

/-- A continuous left `N`-invariant function supported on `N C`, `C` compact, is integrable
on the quotient through its representatives. -/
theorem integrable_out_of_compact_support (φ : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (L : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hφL : ∀ g l, l ∈ L → φ (g * l) = φ g)
    (hφN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, φ (u.val * g) = φ g)
    (C : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) (hC : IsCompact C)
    (hsupp : ∀ g, φ g ≠ 0 → ∃ u : upperUnipotent (m + 1) F.Carrier, u.val * g ∈ C) :
    Integrable (fun q : LeftQuotient (upperUnipotent (m + 1) F.Carrier) => φ q.out)
      (unipotentQuotientHaar F.Carrier m) := by
  have hcompat := unipotentQuotientHaar_isCompatible F.Carrier m
  have : (unipotentQuotientHaar F.Carrier m).Regular := hcompat.regular
  have := localField_t2 F.Carrier
  have := leftQuotient_t2Space (upperUnipotent (m + 1) F.Carrier)
    (UpperUnipotent.isClosed (R := F.Carrier))
  have hφc : Continuous φ :=
    LastRowReductionLocal.continuous_of_rightInvariant L φ (fun x j hj => hφL x j hj)
  set φq := QuotientIntegration.descend _ φ hφN with hφq
  have heq : (fun q : LeftQuotient (upperUnipotent (m + 1) F.Carrier) => φ q.out) = φq := by
    funext q
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  have hφqc : Continuous φq :=
    (leftQuotient_isOpenQuotientMap (upperUnipotent (m + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
      hφc
  have himg : IsCompact ((leftQuotientMap (upperUnipotent (m + 1) F.Carrier)) '' C) :=
    hC.image (leftQuotient_isOpenQuotientMap _).continuous
  have hcs : HasCompactSupport φq := by
    refine HasCompactSupport.intro himg fun q hq => ?_
    by_contra hne
    apply hq
    have hne' : φ q.out ≠ 0 := by
      rw [show φ q.out = φq q from congrFun heq q]
      exact hne
    obtain ⟨u, hu⟩ := hsupp _ hne'
    refine ⟨u.val * q.out, hu, ?_⟩
    conv_rhs => rw [← Quotient.out_eq q]
    apply Quotient.sound
    change QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply]
    simp
  rw [heq]
  exact hφqc.integrable_of_hasCompactSupport hcs

variable {ω : F.Carrierˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)

/-- The weighted right average of the target is `vol(K⁰(f))` times the target. -/
theorem rightAverage_firstColumnTarget (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F.Carrier →* ℂˣ)
    (hψN : ∀ n : upperUnipotent (m + 1) F.Carrier,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F.Carrier).integer) → ψN n = 1)
    (L : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hL : ∀ g l, l ∈ L → firstColumnTarget ω hf ψN (g * l) = firstColumnTarget ω hf ψN g)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    rightAverage (generalLinearHaar F.Carrier m) (firstColumnTarget ω hf ψN) L hL
        (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) g =
      ((generalLinearHaar F.Carrier m).real
        (firstColumnOpenSubgroup F.Carrier m f : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :
          ℂ) * firstColumnTarget ω hf ψN g := by
  rw [rightAverage_apply]
  have hpt : (fun k => firstColumnWeight ω hf k * firstColumnTarget ω hf ψN (g * k)) =
      (firstColumnOpenSubgroup F.Carrier m f :
        Set (Langlands.GeneralLinear (m + 1) F.Carrier)).indicator
        (fun _ => firstColumnTarget ω hf ψN g) := by
    funext k
    by_cases hk : k ∈ (firstColumnOpenSubgroup F.Carrier m f :
        Set (Langlands.GeneralLinear (m + 1) F.Carrier))
    · have hk' : InFirstColumn f k := hk
      rw [Set.indicator_of_mem hk, firstColumnWeight_of_mem ω hf hk',
        firstColumnTarget_mul_firstColumn hf hω ψN hψN g hk']
      have : ((ω (firstEntryUnit hf k hk') : ℂ)) ≠ 0 := Units.ne_zero _
      field_simp
    · rw [Set.indicator_of_notMem hk, firstColumnWeight_of_not_mem ω hf hk, zero_mul]
  rw [hpt, integral_indicator_const _
    (firstColumnOpenSubgroup F.Carrier m f).isOpen.measurableSet]
  simp

/-- The quotient pairing of the target with `W` is `∫_(K⁰(f)) ω(k₀₀) W(k) dk`. -/
theorem integral_firstColumnTarget_pair (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F.Carrier →* ℂˣ)
    (hψN : ∀ n : upperUnipotent (m + 1) F.Carrier,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F.Carrier).integer) → ψN n = 1)
    (W : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LW : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hWL : ∀ g l, l ∈ LW → W (g * l) = W g)
    (hWN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, W (u.val * g) = ((ψN u : ℂ))⁻¹ * W g) :
    ∫ q, firstColumnTarget ω hf ψN q.out * W q.out ∂unipotentQuotientHaar F.Carrier m =
      ∫ k, (firstColumnOpenSubgroup F.Carrier m f :
          Set (Langlands.GeneralLinear (m + 1) F.Carrier)).indicator
        (fun k => (firstColumnCharacter ω hf k)⁻¹ * W k) k ∂generalLinearHaar F.Carrier m := by
  have hcompat := unipotentQuotientHaar_isCompatible F.Carrier m
  have hφc : Continuous (fun g => firstColumnTarget ω hf ψN g * W g) := by
    apply LastRowReductionLocal.continuous_of_rightInvariant
      (LW ⊓ Conductor.principalLevelOpenSubgroup F.Carrier m f)
    intro g l hl
    rw [hWL g l hl.1, firstColumnTarget_mul_principal hf hω ψN hψN g l hl.2]
  rw [integral_out_of_support (upperUnipotent (m + 1) F.Carrier) (generalLinearHaar F.Carrier m)
    (unipotentHaar F.Carrier m) _ hcompat (firstColumnOpenSubgroup F.Carrier m f)
    (isCompact_firstColumnOpenSubgroup F.Carrier m f) (unipotentHaar_firstColumn F) _ hφc
    (fun u g => by
      rw [hWN, firstColumnTarget_unipotent_mul hf hω ψN hψN]
      field_simp)
    (fun g hg => by
      have ht : firstColumnTarget ω hf ψN g ≠ 0 := left_ne_zero_of_mul hg
      obtain ⟨u, hu⟩ := firstColumnTarget_support hf ψN ht
      exact ⟨u, hu⟩)]
  congr 1
  funext k
  by_cases hk : k ∈ (firstColumnOpenSubgroup F.Carrier m f :
      Set (Langlands.GeneralLinear (m + 1) F.Carrier))
  · have hk' : InFirstColumn f k := hk
    rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, firstColumnCharacter_of_mem ω hf hk',
      inv_inv]
    have h2 := firstColumnTarget_mul hf hω ψN hψN 1 hk'
    simp only [OneMemClass.coe_one, one_mul, map_one, Units.val_one] at h2
    rw [h2]
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]

/-- The inverse average as an integral: `W_avg(g) = ∫ w(k) W(g k⁻¹) dk`. -/
theorem inverseAverage_apply (μG : Measure (Langlands.GeneralLinear (m + 1) F.Carrier))
    [IsFiniteMeasureOnCompacts μG] (W : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (L : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hW : ∀ g l, l ∈ L → W (g * l) = W g)
    (w : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ) (hw : IsLocallyConstant w)
    (hwc : HasCompactSupport w) (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    inverseAverage μG W L hW w hw hwc g = ∫ k, w k * W (g * k⁻¹) ∂μG := by
  have hfin : (inverseTranslates W L hW w hw hwc).FinMeasSupp μG :=
    compactlySupportedSimpleFunc_finMeasSupp μG _ _ _
  have := AlgebraicIntegral.integral_linearMap _ hfin
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear (m + 1) F.Carrier => ℂ) g)
  calc inverseAverage μG W L hW w hw hwc g =
      (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear (m + 1) F.Carrier => ℂ) g)
        (AlgebraicIntegral.integral μG (inverseTranslates W L hW w hw hwc)) := rfl
    _ = _ := this.symm
    _ = ∫ k, w k * W (g * k⁻¹) ∂μG := by
      rw [AlgebraicIntegral.integral_eq_bochner _ (hfin.map (LinearMap.proj g).map_zero)]
      congr 1

/-- The inverse average of a left `(N, ψ_N⁻¹)`-equivariant function, with the weight of
`K⁰(f)`, is again equivariant and is right invariant under the principal congruence
subgroup of level `f`. -/
theorem inverseAverage_firstColumn_properties (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F.Carrier →* ℂˣ)
    (W : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LW : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hWL : ∀ g l, l ∈ LW → W (g * l) = W g)
    (hWN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, W (u.val * g) = ((ψN u : ℂ))⁻¹ * W g) :
    (∀ (u : upperUnipotent (m + 1) F.Carrier) g,
      inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
          (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) (u.val * g) =
        ((ψN u : ℂ))⁻¹ * inverseAverage (generalLinearHaar F.Carrier m) W LW hWL
          (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) g) ∧
    (∀ g l, l ∈ Conductor.principalLevelOpenSubgroup F.Carrier m f →
      inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
          (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) (g * l) =
        inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
          (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) g) := by
  refine ⟨fun u g => ?_, fun g l hl => ?_⟩
  · rw [inverseAverage_apply, inverseAverage_apply, ← integral_const_mul]
    congr 1
    funext k
    rw [mul_assoc, hWN]
    ring
  · rw [inverseAverage_apply, inverseAverage_apply]
    rw [← integral_mul_right_eq_self (fun k => firstColumnWeight ω hf k * W (g * l * k⁻¹)) l]
    congr 1
    funext k
    rw [firstColumnWeight_mul_principal hf hω k l hl]
    congr 2
    group

/-- `∫_(K⁰(f)) ω(k₀₀) W_avg(k) dk = vol(K⁰(f)) ∫ t W` for the inverse average `W_avg`. -/
theorem integral_firstColumn_inverseAverage (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F.Carrier →* ℂˣ)
    (hψN : ∀ n : upperUnipotent (m + 1) F.Carrier,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F.Carrier).integer) → ψN n = 1)
    (W : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LW : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hWL : ∀ g l, l ∈ LW → W (g * l) = W g)
    (hWN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, W (u.val * g) = ((ψN u : ℂ))⁻¹ * W g) :
    ∫ k, (firstColumnOpenSubgroup F.Carrier m f :
          Set (Langlands.GeneralLinear (m + 1) F.Carrier)).indicator
        (fun k => (firstColumnCharacter ω hf k)⁻¹ *
          inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
            (firstColumnWeight_isLocallyConstant F hf hω)
            (firstColumnWeight_hasCompactSupport F hf) k) k ∂generalLinearHaar F.Carrier m =
      ((generalLinearHaar F.Carrier m).real
        (firstColumnOpenSubgroup F.Carrier m f : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :
          ℂ) *
        ∫ q, firstColumnTarget ω hf ψN q.out * W q.out ∂unipotentQuotientHaar F.Carrier m := by
  have hcompat := unipotentQuotientHaar_isCompatible F.Carrier m
  obtain ⟨hAN, hAL⟩ := inverseAverage_firstColumn_properties F hf hω ψN W LW hWL hWN
  set Wavg := inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
    (firstColumnWeight_isLocallyConstant F hf hω) (firstColumnWeight_hasCompactSupport F hf)
    with hWavg
  rw [← integral_firstColumnTarget_pair F hf hω ψN hψN Wavg
    (Conductor.principalLevelOpenSubgroup F.Carrier m f) hAL hAN]
  have htL : ∀ g l, l ∈ Conductor.principalLevelOpenSubgroup F.Carrier m f →
      firstColumnTarget ω hf ψN (g * l) = firstColumnTarget ω hf ψN g :=
    fun g l hl => firstColumnTarget_mul_principal hf hω ψN hψN g l hl
  have hpair := integral_rightAverage_pair (unipotentQuotientHaar F.Carrier m)
    hcompat.right_invariant (generalLinearHaar F.Carrier m) (firstColumnTarget ω hf ψN) W
    (Conductor.principalLevelOpenSubgroup F.Carrier m f) LW htL hWL (firstColumnWeight ω hf)
    (firstColumnWeight_isLocallyConstant F hf hω) (firstColumnWeight_hasCompactSupport F hf)
    (fun h g k => by
      rw [mul_assoc, firstColumnTarget_unipotent_mul hf hω ψN hψN, hWN]
      field_simp)
    (fun k => by
      set Lk : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier) :=
        Conductor.principalLevelOpenSubgroup F.Carrier m f ⊓
          LW.comap (MulAut.conj k).toMonoidHom
            ((continuous_const.mul continuous_id).mul continuous_const)
      refine integrable_out_of_compact_support F
        (fun g => firstColumnTarget ω hf ψN g * W (g * k⁻¹)) Lk ?_ ?_
        (firstColumnOpenSubgroup F.Carrier m f) (isCompact_firstColumnOpenSubgroup F.Carrier m f) ?_
      · intro g l hl
        have hl2 : k * l * k⁻¹ ∈ LW := hl.2
        rw [htL g l hl.1]
        congr 1
        rw [show g * l * k⁻¹ = g * k⁻¹ * (k * l * k⁻¹) by group, hWL _ _ hl2]
      · intro u g
        rw [firstColumnTarget_unipotent_mul hf hω ψN hψN,
          show u.val * g * k⁻¹ = u.val * (g * k⁻¹) from mul_assoc _ _ _, hWN]
        field_simp
      · intro g hg
        have ht : firstColumnTarget ω hf ψN g ≠ 0 := left_ne_zero_of_mul hg
        obtain ⟨u, hu⟩ := firstColumnTarget_support hf ψN ht
        exact ⟨u, hu⟩)
  rw [← hpair]
  simp_rw [rightAverage_firstColumnTarget F hf hω ψN hψN]
  rw [← integral_const_mul]
  congr 1
  funext q
  ring

end Measure

end Langlands.RankinSelberg.HighlyRamified
