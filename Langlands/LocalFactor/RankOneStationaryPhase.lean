import Langlands.LocalFactor.RankOneLinearization

noncomputable section

open MeasureTheory
open scoped Topology WithZero

namespace Langlands.LocalFactor.RankOneStability

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

open PadicAbelian HarmonicAnalysis.AdditiveSelfDuality
attribute [local instance] Classical.propDecidable

abbrev DeepQuotient (m a : ℕ) :=
  T.additiveLattice (-(m : ℤ)) ⧸
    (T.additiveLattice (-(a : ℤ))).addSubgroupOf (T.additiveLattice (-(m : ℤ)))

@[instance_reducible] def deepQuotientFintype (m a : ℕ) :
    Fintype (DeepQuotient T m a) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : CompactSpace (T.additiveLattice (-(m : ℤ))) :=
    isCompact_iff_compactSpace.mp (T.isCompact_additiveLattice _)
  exact @Fintype.ofFinite _ (by
    apply AddSubgroup.quotient_finite_of_isOpen
    rw [AddSubgroup.coe_addSubgroupOf]
    exact (T.isOpen_additiveLattice _).preimage continuous_subtype_val)

theorem sum_deep_phases (ψ : AdditiveCharacter) (a m : ℕ) (z : F.Carrier)
    (hz : z ∈ T.additiveLattice (T.additiveConductor ψ + a)) :
    letI := T.topology
    letI := deepQuotientFintype T m a
    ∑ q : DeepQuotient T m a, ψ.complex (z * q.out.val) =
      if z ∈ T.additiveLattice (T.additiveConductor ψ + m)
      then (Fintype.card (DeepQuotient T m a) : ℂ) else 0 := by
  let := T.topology
  let := deepQuotientFintype T m a
  classical
  let G := T.additiveLattice (-(m : ℤ))
  let K := (T.additiveLattice (-(a : ℤ))).addSubgroupOf G
  let φ : AddChar G ℂ := (ψ.complex.mulShift z).compAddMonoidHom G.subtype
  have hφ : ∀ x : G, φ x = ψ.complex (z * x.val) := fun _ => rfl
  have hK : ∀ x ∈ K, φ x = 1 := by
    intro x hx
    rw [hφ]
    apply T.complex_eq_one_of_mem_conductor ψ
    have h := T.mul_mem_additiveLattice_add hz (AddSubgroup.mem_addSubgroupOf.mp hx)
    simpa only [add_neg_cancel_right] using h
  let Φ := quotientAddChar K φ hK
  have hΦ : ∀ q : DeepQuotient T m a, Φ q = ψ.complex (z * q.out.val) := by
    intro q
    conv_lhs => rw [← Quotient.out_eq' q]
    rfl
  have hzero : Φ = 0 ↔ z ∈ T.additiveLattice (T.additiveConductor ψ + m) := by
    constructor
    · intro h
      have htriv : ∀ x ∈ T.additiveLattice (-(m : ℤ)), ψ.complex (z * x) = 1 := by
        intro x hx
        have hh := congrArg (fun c : AddChar (G ⧸ K) ℂ =>
          c ((⟨x, hx⟩ : G) : G ⧸ K)) h
        exact hh
      simpa only [sub_neg_eq_add] using
        T.mem_additiveLattice_of_forall_complex_mul_eq_one ψ (-(m : ℤ)) z htriv
    · intro h
      ext q
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      change ψ.complex (z * x.val) = 1
      apply T.complex_eq_one_of_mem_conductor ψ
      have hh := T.mul_mem_additiveLattice_add h x.property
      simpa only [add_neg_cancel_right] using hh
  calc
    _ = ∑ q : DeepQuotient T m a, Φ q := by
      apply Finset.sum_congr rfl
      intro q _
      exact (hΦ q).symm
    _ = _ := by simp only [AddChar.sum_eq_ite, hzero]

theorem gauss_rotation_phase (χ : Character) (ψ : AdditiveCharacter)
    {m : ℕ} (hm : 0 < m) (c : F.Carrier)
    (hlin : letI := T.topology; ∀ h : T.additiveLattice (-(m : ℤ)),
      (χ (oneAddUnit T hm h) : ℂ) = ψ.complex (c * h.val))
    (h : T.additiveLattice (-(m : ℤ))) (x : F.Carrier) :
    letI := T.topology
    gaussIntegrand T χ ψ.toAddChar 0 ((oneAddUnit T hm h : F.Carrier) * x) =
      ψ.complex ((x - c) * h.val) * gaussIntegrand T χ ψ.toAddChar 0 x := by
  let := T.topology
  rw [gaussIntegrand_zero_apply, gaussIntegrand_zero_apply, characterExtension_unit_mul,
    hlin, mul_inv]
  change (ψ.complex (c * h.val))⁻¹ * (characterExtension T χ x)⁻¹ *
    ψ.complex ((oneAddUnit T hm h : F.Carrier) * x) =
    ψ.complex ((x - c) * h.val) * ((characterExtension T χ x)⁻¹ * ψ.complex x)
  rw [← AddChar.map_neg_eq_inv]
  calc
    _ = (characterExtension T χ x)⁻¹ *
        ψ.complex (-(c * h.val) + (1 + h.val) * x) := by
      rw [AddChar.map_add_eq_mul]
      simp only [oneAddUnit_val]
      ring
    _ = (characterExtension T χ x)⁻¹ *
        ψ.complex (((x - c) * h.val) + x) := by congr 2; ring
    _ = _ := by rw [AddChar.map_add_eq_mul]; ring

/-- Finite averaging cuts the Gauss integral down to the annihilator coset. -/
theorem gauss_integral_localized (χ : Character) (ψ : AdditiveCharacter) (μ : LocalHaar)
    (a : ℕ) {m : ℕ} (hm : 0 < m) (c : F.Carrier)
    (hcmem : c ∈ T.additiveLattice (T.additiveConductor ψ + a))
    (hlin : letI := T.topology; ∀ h : T.additiveLattice (-(m : ℤ)),
      (χ (oneAddUnit T hm h) : ℂ) = ψ.complex (c * h.val)) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x in gaussShell T (T.additiveConductor ψ + a),
        gaussIntegrand T χ ψ.toAddChar 0 x ∂μ.measure =
      ∫ x in gaussShell T (T.additiveConductor ψ + a),
        if x - c ∈ T.additiveLattice (T.additiveConductor ψ + m)
        then gaussIntegrand T χ ψ.toAddChar 0 x else 0 ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := deepQuotientFintype T m a
  let S := gaussShell T (T.additiveConductor ψ + a)
  let g := gaussIntegrand T χ ψ.toAddChar 0
  let phase := fun (q : DeepQuotient T m a) (x : F.Carrier) =>
    ψ.complex ((x - c) * q.out.val)
  have hint (q : DeepQuotient T m a) :
      IntegrableOn (fun x => phase q x * g x) S μ.measure := by
    rw [show S = T.valuationShell (T.additiveConductor ψ + a) by
      exact gaussShell_eq_valuationShell T _]
    apply ContinuousOn.integrableOn_compact'
      (T.valuationShell_compact_closed _).1
      (T.valuationShell_compact_closed _).2.measurableSet
    have hp : Continuous (phase q) := ψ.continuous_complex.comp
      ((continuous_id.sub continuous_const).mul continuous_const)
    apply hp.continuousOn.mul
    dsimp [g]
    rw [gaussIntegrand_zero]
    exact (HarmonicAnalysis.Quasicharacter.continuousOn_epsilonIntegrand χ ψ).mono
      (fun _x hx => T.valuationShell_ne_zero _ hx)
  have hI (q : DeepQuotient T m a) :
      ∫ x in S, phase q x * g x ∂μ.measure = ∫ x in S, g x ∂μ.measure := by
    calc
      _ = ∫ x in S, g ((oneAddUnit T hm q.out : F.Carrier) * x) ∂μ.measure := by
        apply setIntegral_congr_fun (gaussShell_measurableSet T _)
        intro x _
        exact (gauss_rotation_phase T χ ψ hm c hlin q.out x).symm
      _ = _ := by
        apply setIntegral_gaussShell_mul_unit T μ
        have hv := (oneAddUnit_mem T hm q.out).1
        rw [gauss_valuation_eq_exp_neg_ord T (oneAddUnit T hm q.out).ne_zero,
          ← WithZero.exp_zero] at hv
        have hh := WithZero.exp_injective hv
        omega
  have hsum (x : F.Carrier) (hx : x ∈ S) :
      ∑ q : DeepQuotient T m a, phase q x =
        if x - c ∈ T.additiveLattice (T.additiveConductor ψ + m)
        then (Fintype.card (DeepQuotient T m a) : ℂ) else 0 := by
    apply sum_deep_phases T ψ a m
    apply (T.additiveLattice _).sub_mem _ hcmem
    rw [T.mem_additiveLattice, gauss_valuation_eq_exp_neg_ord T hx.1, hx.2, neg_neg]
  have hcard : (Fintype.card (DeepQuotient T m a) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  calc
    _ = ∑ _q : DeepQuotient T m a, ∫ x in S, g x ∂μ.measure := by simp [S, g]
    _ = ∑ q : DeepQuotient T m a, ∫ x in S, phase q x * g x ∂μ.measure := by
      apply Finset.sum_congr rfl
      intro q _
      exact (hI q).symm
    _ = ∫ x in S, ∑ q : DeepQuotient T m a, phase q x * g x ∂μ.measure :=
      (integral_finsetSum _ (fun q _ => hint q)).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun (gaussShell_measurableSet T _)
      intro x hx
      dsimp only
      rw [← Finset.sum_mul, hsum x hx]
      by_cases h : x - c ∈ T.additiveLattice (T.additiveConductor ψ + m) <;> simp [h, g]

theorem localized_ratio_mem (ψ : AdditiveCharacter) (a m k : ℕ) (hlevels : a = m + k)
    (c x : F.Carrierˣ)
    (hc : T.ord (c : F.Carrier) = -(T.additiveConductor ψ + a))
    (hx : T.ord (x : F.Carrier) = -(T.additiveConductor ψ + a))
    (h : (x : F.Carrier) - c ∈ T.additiveLattice (T.additiveConductor ψ + m)) :
    x * c⁻¹ ∈ T.principalUnits k := by
  have hvc : T.discreteValuation (c : F.Carrier) =
      WithZero.exp (T.additiveConductor ψ + a) := by
    rw [gauss_valuation_eq_exp_neg_ord T c.ne_zero, hc, neg_neg]
  have hvx : T.discreteValuation (x : F.Carrier) =
      WithZero.exp (T.additiveConductor ψ + a) := by
    rw [gauss_valuation_eq_exp_neg_ord T x.ne_zero, hx, neg_neg]
  constructor
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hvx, hvc,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  · have heq : ((x * c⁻¹ : F.Carrierˣ) : F.Carrier) - 1 =
        ((x : F.Carrier) - c) * (c : F.Carrier)⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    rw [heq, map_mul, map_inv₀, hvc]
    calc
      _ ≤ WithZero.exp (T.additiveConductor ψ + m) *
          (WithZero.exp (T.additiveConductor ψ + a))⁻¹ := mul_le_mul' h le_rfl
      _ = _ := by
        rw [← WithZero.exp_neg, ← WithZero.exp_add]
        congr 1
        omega

/-- On the localized coset, a lower-conductor twist is constant. -/
theorem gauss_twist_on_localized (χ η : Character) (ψ : AdditiveCharacter)
    (a m k : ℕ) (hlevels : a = m + k)
    (hη : T.multiplicativeConductor η ≤ k) (c : F.Carrierˣ)
    (hc : T.ord (c : F.Carrier) = -(T.additiveConductor ψ + a))
    (x : F.Carrier) (hx : x ∈ gaussShell T (T.additiveConductor ψ + a))
    (h : x - c ∈ T.additiveLattice (T.additiveConductor ψ + m)) :
    letI := T.topology
    gaussIntegrand T (χ * η) ψ.toAddChar 0 x =
      (η c⁻¹ : ℂ) * gaussIntegrand T χ ψ.toAddChar 0 x := by
  let := T.topology
  let v := Units.mk0 x hx.1
  have hratio : v * c⁻¹ ∈ T.principalUnits k :=
    localized_ratio_mem T ψ a m k hlevels c v hc hx.2 h
  have hηratio := ((T.multiplicativeTrivialAt_iff_conductor_le η k).mpr hη) _ hratio
  have hηv : η v = η c := by
    rw [map_mul, map_inv] at hηratio
    exact (mul_inv_eq_one.mp hηratio)
  rw [gaussIntegrand_zero_apply, gaussIntegrand_zero_apply]
  have hchar : characterExtension T (χ * η) x =
      characterExtension T χ x * (η c : ℂ) := by
    have hval (κ : Character) : characterExtension T κ x = (κ v : ℂ) :=
      by simp [characterExtension, hx.1, v]
    rw [hval, hval]
    change ((χ v * η v : ℂˣ) : ℂ) = (χ v : ℂ) * (η c : ℂ)
    rw [hηv, Units.val_mul]
  rw [hchar, mul_inv, map_inv, Units.val_inv_eq_inv_val]
  ring

/-- The linearizing element gives the unshifted Gauss twist identity. -/
theorem gauss_integral_twist (χ η : Character) (ψ : AdditiveCharacter) (μ : LocalHaar)
    (a m k : ℕ) (hm : 0 < m) (hlevels : a = m + k)
    (hηk : T.multiplicativeConductor η ≤ k)
    (hηm : T.multiplicativeConductor η ≤ m) (c : F.Carrierˣ)
    (hc : T.ord (c : F.Carrier) = -(T.additiveConductor ψ + a))
    (hlin : letI := T.topology; ∀ h : T.additiveLattice (-(m : ℤ)),
      (χ (oneAddUnit T hm h) : ℂ) = ψ.complex ((c : F.Carrier) * h.val)) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x in gaussShell T (T.additiveConductor ψ + a),
        gaussIntegrand T (χ * η) ψ.toAddChar 0 x ∂μ.measure =
      (η c⁻¹ : ℂ) *
        ∫ x in gaussShell T (T.additiveConductor ψ + a),
          gaussIntegrand T χ ψ.toAddChar 0 x ∂μ.measure := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have hcmem : (c : F.Carrier) ∈ T.additiveLattice (T.additiveConductor ψ + a) := by
    rw [T.mem_additiveLattice, gauss_valuation_eq_exp_neg_ord T c.ne_zero, hc, neg_neg]
  have hlin' : ∀ h : T.additiveLattice (-(m : ℤ)),
      ((χ * η) (oneAddUnit T hm h) : ℂ) = ψ.complex ((c : F.Carrier) * h.val) := by
    intro h
    change ((χ (oneAddUnit T hm h) * η (oneAddUnit T hm h) : ℂˣ) : ℂ) = _
    rw [((T.multiplicativeTrivialAt_iff_conductor_le η m).mpr hηm) _
      (oneAddUnit_mem T hm h), mul_one]
    exact hlin h
  rw [gauss_integral_localized T (χ * η) ψ μ a hm c hcmem hlin',
    gauss_integral_localized T χ ψ μ a hm c hcmem hlin, ← integral_const_mul]
  apply setIntegral_congr_fun (gaussShell_measurableSet T _)
  intro x hx
  dsimp only
  by_cases h : x - (c : F.Carrier) ∈ T.additiveLattice (T.additiveConductor ψ + m)
  · simp only [h, ite_true]
    exact gauss_twist_on_localized T χ η ψ a m k hlevels hηk c hc x hx h
  · simp only [h, ite_false, mul_zero]

end Langlands.LocalFactor.RankOneStability
