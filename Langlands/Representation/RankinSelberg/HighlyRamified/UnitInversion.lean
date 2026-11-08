import Langlands.Representation.RankinSelberg.HighlyRamified.DualWeightSum

/-!
# Finite Fourier inversion in one variable

For an additive character `ψ` of conductor `O`, a unit `ϖ ∈ O` and `b ≥ 0`, every function
`S₁` on `O` that is periodic modulo `ϖ^b O` is a finite exponential sum
`S₁(ξ) = Σ_(u ∈ T₁) Φ₁(u) ψ(u ξ)` on `O`, with `T₁ ⊆ ϖ^(-b) O` finite. This is the inverse
Fourier transform on the finite group `O / ϖ^b O`. It produces the first component of the test
function of Jacquet and Shalika (1985), (4.4.6).
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis

universe uF

section Periodic

variable {F : Type*} [AddCommGroup F] [MeasurableSpace F] [MeasurableAdd F]

/-- The integral over `K` of an `L`-periodic function is `vol(L)` times its sum over finite
representatives of `K` modulo `L`. -/
theorem integral_periodic_eq_sum (μ : Measure F) [μ.IsAddRightInvariant]
    (K L : AddSubgroup F) (hLK : L ≤ K) (hLm : MeasurableSet (L : Set F))
    (hLfin : μ (L : Set F) < ⊤) (T : Finset F) (hTK : (T : Set F) ⊆ K)
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L → t = t') (hcov : ∀ v ∈ K, ∃ t ∈ T, v - t ∈ L)
    (φ : F → ℂ) (hφ : ∀ x l, l ∈ L → φ (x + l) = φ x) :
    ∫ x, (K : Set F).indicator φ x ∂μ = (μ (L : Set F)).toReal * ∑ t ∈ T, φ t := by
  classical
  set S : F → Set F := fun t => (fun x => x + -t) ⁻¹' (L : Set F) with hS
  have hSmem : ∀ t x, x ∈ S t ↔ x - t ∈ L := by
    intro t x
    simp [hS, sub_eq_add_neg]
  have hSm : ∀ t, MeasurableSet (S t) := fun t => hLm.preimage (measurable_add_const (-t))
  have hSμ : ∀ t, μ (S t) = μ (L : Set F) := fun t => measure_preimage_add_right μ (-t) _
  have hdec : (K : Set F).indicator φ = fun x => ∑ t ∈ T, (S t).indicator (fun _ => φ t) x := by
    funext x
    by_cases hx : x ∈ (K : Set F)
    · rw [Set.indicator_of_mem hx]
      obtain ⟨t₀, ht₀, hxt⟩ := hcov x hx
      rw [Finset.sum_eq_single t₀]
      · rw [Set.indicator_of_mem ((hSmem t₀ x).2 hxt)]
        have := hφ t₀ (x - t₀) hxt
        rwa [add_sub_cancel] at this
      · intro t ht hne
        rw [Set.indicator_of_notMem]
        intro hxS
        apply hne
        apply hT t ht t₀ ht₀
        have := L.sub_mem hxt ((hSmem t x).1 hxS)
        rwa [sub_sub_sub_cancel_left] at this
      · intro h; exact absurd ht₀ h
    · rw [Set.indicator_of_notMem hx]
      refine (Finset.sum_eq_zero fun t ht => ?_).symm
      rw [Set.indicator_of_notMem]
      intro hxS
      apply hx
      have := K.add_mem (hLK ((hSmem t x).1 hxS)) (hTK ht)
      rwa [sub_add_cancel] at this
  rw [hdec, integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_indicator_const _ (hSm t), measureReal_def, hSμ t, Complex.real_smul]
  · intro t _
    have hfin : μ (S t) ≠ ⊤ := by rw [hSμ t]; exact hLfin.ne
    exact (integrableOn_const hfin).integrable_indicator (hSm t)

/-- Shift invariance of sums over representatives: for an `L`-periodic `g` and `δ ∈ K`,
`Σ_(t ∈ T) g(t + δ) = Σ_(t ∈ T) g(t)`. -/
theorem sum_reps_shift (μ : Measure F) [μ.IsAddRightInvariant]
    (K L : AddSubgroup F) (hLK : L ≤ K) (hLm : MeasurableSet (L : Set F))
    (hLfin : μ (L : Set F) < ⊤) (hLpos : 0 < μ (L : Set F)) (T : Finset F)
    (hTK : (T : Set F) ⊆ K) (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L → t = t')
    (hcov : ∀ v ∈ K, ∃ t ∈ T, v - t ∈ L)
    (g : F → ℂ) (hg : ∀ x l, l ∈ L → g (x + l) = g x) (δ : F) (hδ : δ ∈ K) :
    ∑ t ∈ T, g (t + δ) = ∑ t ∈ T, g t := by
  have h1 := integral_periodic_eq_sum μ K L hLK hLm hLfin T hTK hT hcov (fun x => g (x + δ))
    (fun x l hl => by rw [add_right_comm, hg _ l hl])
  have h2 := integral_periodic_eq_sum μ K L hLK hLm hLfin T hTK hT hcov g hg
  have hind : (K : Set F).indicator (fun x => g (x + δ)) =
      fun x => (K : Set F).indicator g (x + δ) := by
    funext x
    by_cases hx : x ∈ (K : Set F)
    · have hxδ : x + δ ∈ (K : Set F) := K.add_mem hx hδ
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxδ]
    · have hxδ : x + δ ∉ (K : Set F) := fun h => hx (by simpa using K.sub_mem h hδ)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxδ]
  rw [hind, integral_add_right_eq_self (fun x => (K : Set F).indicator g x) δ, h2] at h1
  have hvol : ((μ (L : Set F)).toReal : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (ENNReal.toReal_pos hLpos.ne' hLfin.ne).ne'
  exact (mul_left_cancel₀ hvol h1).symm

end Periodic

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance unitInversionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance unitInversionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance unitInversionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance unitInversionFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance unitInversionFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩

/-- The lattice `a⁻¹ O = {u : a u ∈ O}`. For `a = ϖ^b` it is `ϖ^(-b) O`, and
`scaledIntegers F a⁻¹ = a O = ϖ^b O`. -/
def scaledIntegers (a : F.Carrierˣ) : AddSubgroup F.Carrier where
  carrier := {u | (a : F.Carrier) * u ∈ (ValuativeRel.valuation F.Carrier).integer}
  add_mem' := fun {x y} hx hy => by
    show (a : F.Carrier) * (x + y) ∈ (ValuativeRel.valuation F.Carrier).integer
    rw [mul_add]
    exact Subring.add_mem _ hx hy
  zero_mem' := by
    show (a : F.Carrier) * 0 ∈ (ValuativeRel.valuation F.Carrier).integer
    rw [mul_zero]
    exact Subring.zero_mem _
  neg_mem' := fun {x} hx => by
    show (a : F.Carrier) * -x ∈ (ValuativeRel.valuation F.Carrier).integer
    rw [mul_neg]
    exact Subring.neg_mem _ hx

theorem mem_scaledIntegers {a : F.Carrierˣ} {u : F.Carrier} :
    u ∈ scaledIntegers F a ↔ (a : F.Carrier) * u ∈ (ValuativeRel.valuation F.Carrier).integer :=
  Iff.rfl

theorem isOpen_scaledIntegers (a : F.Carrierˣ) :
    IsOpen (scaledIntegers F a : Set F.Carrier) :=
  (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).preimage
    (continuous_const.mul continuous_id)

theorem isCompact_scaledIntegers (a : F.Carrierˣ) :
    IsCompact (scaledIntegers F a : Set F.Carrier) := by
  have hO : IsCompact ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) :=
    isCompact_integer F
  have himg := hO.image (f := fun x : F.Carrier => (a⁻¹ : F.Carrierˣ) * x)
    (continuous_const.mul continuous_id)
  convert himg using 1
  ext u
  simp only [SetLike.mem_coe, mem_scaledIntegers, Set.mem_image]
  constructor
  · intro hu
    exact ⟨(a : F.Carrier) * u, hu, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

theorem integer_le_scaledIntegers {a : F.Carrierˣ}
    (ha : (a : F.Carrier) ∈ (ValuativeRel.valuation F.Carrier).integer) :
    integerAddSubgroup F ≤ scaledIntegers F a := fun _ hu =>
  Subring.mul_mem _ ha hu

open Classical in
/-- The character sum `Σ_(u ∈ T₁) ψ(u t)` over representatives of `a⁻¹ O / O`, for integral
`t`: it is `|T₁|` if `t ∈ a O` and `0` otherwise. -/
theorem sum_reps_character (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ) (η : AdditiveHaarMeasure F.Carrier) (a : F.Carrierˣ)
    (ha : (a : F.Carrier) ∈ (ValuativeRel.valuation F.Carrier).integer)
    (T₁ : Finset F.Carrier) (hT₁K : (T₁ : Set F.Carrier) ⊆ scaledIntegers F a)
    (hT₁ : ∀ t ∈ T₁, ∀ t' ∈ T₁, t - t' ∈ integerAddSubgroup F → t = t')
    (hcov : ∀ v ∈ scaledIntegers F a, ∃ t ∈ T₁, v - t ∈ integerAddSubgroup F)
    (t : F.Carrier) (ht : t ∈ (ValuativeRel.valuation F.Carrier).integer) :
    ∑ u ∈ T₁, ψ.complex (u * t) =
      if t ∈ scaledIntegers F a⁻¹ then (T₁.card : ℂ) else 0 := by
  classical
  set K := scaledIntegers F a with hKdef
  set O := integerAddSubgroup F with hOdef
  have hOm : MeasurableSet (O : Set F.Carrier) :=
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).measurableSet
  have hOfin : η.measure (O : Set F.Carrier) < ⊤ := (isCompact_integer F).measure_lt_top
  have hOpos : 0 < η.measure (O : Set F.Carrier) :=
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).measure_pos _
      ⟨0, Subring.zero_mem _⟩
  have hvol : ((η.measure (O : Set F.Carrier)).toReal : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  have hle := integer_le_scaledIntegers F ha
  -- the periodic sums as integrals
  have hφ := integral_periodic_eq_sum η.measure K O hle hOm hOfin T₁ hT₁K hT₁ hcov
    (fun u => ψ.complex (u * t)) (fun x l hl => by
      rw [add_mul, AddChar.map_add_eq_mul, show ψ.complex (l * t) = 1 by
        rw [UnitaryAdditiveCharacter.complex_apply, hψ.trivial _ (Subring.mul_mem _ hl ht)]
        simp, mul_one])
  have h1 := integral_periodic_eq_sum η.measure K O hle hOm hOfin T₁ hT₁K hT₁ hcov
    (fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
  have hind : (K : Set F.Carrier).indicator (fun u => ψ.complex (u * t)) =
      fun u => ψ.complex (u * t) * (K : Set F.Carrier).indicator (fun _ => (1 : ℂ)) u := by
    funext u
    by_cases hu : u ∈ (K : Set F.Carrier)
    · simp [Set.indicator_of_mem hu]
    · simp [Set.indicator_of_notMem hu]
  rw [hind] at hφ
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  split_ifs with htL
  · have htriv : ∀ u ∈ K, ψ (u * t) = 1 := by
      intro u hu
      apply hψ.trivial
      have : u * t = ((a : F.Carrier) * u) * ((a⁻¹ : F.Carrierˣ) * t) := by
        rw [Units.val_inv_eq_inv_val]
        field_simp
      rw [this]
      exact Subring.mul_mem _ hu htL
    rw [subgroup_character_integral_of_trivial ψ η K (isOpen_scaledIntegers F a) t htriv] at hφ
    have hK : ((η.measure (K : Set F.Carrier)).toReal : ℂ) =
        ∫ x, (K : Set F.Carrier).indicator (fun _ => (1 : ℂ)) x ∂η.measure := by
      rw [integral_indicator_const _ (isOpen_scaledIntegers F a).measurableSet]
      simp [measureReal_def, hKdef]
    rw [hK, h1] at hφ
    exact (mul_left_cancel₀ hvol hφ).symm
  · have hnot : (a⁻¹ : F.Carrierˣ) * t ∉ (ValuativeRel.valuation F.Carrier).integer := htL
    obtain ⟨z, hz, hne⟩ := hψ.nontrivial _ hnot
    have hu₀ : z * ((a⁻¹ : F.Carrierˣ) : F.Carrier) ∈ K := by
      show (a : F.Carrier) * (z * ((a⁻¹ : F.Carrierˣ) : F.Carrier)) ∈
        (ValuativeRel.valuation F.Carrier).integer
      rw [Units.val_inv_eq_inv_val]
      field_simp
      exact hz
    have hne' : ψ (z * ((a⁻¹ : F.Carrierˣ) : F.Carrier) * t) ≠ 1 := by
      intro h1'
      apply hne
      rw [UnitaryAdditiveCharacter.complex_apply, ← mul_assoc, h1']
      simp
    rw [subgroup_character_integral_of_nontrivial ψ η K t _ hu₀ hne'] at hφ
    have := hφ.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hvol
    · exact h

open Classical in
/-- Finite Fourier inversion on `O / a O` (`a` integral): a function `S₁` on `O` that is
periodic modulo `a O = scaledIntegers F a⁻¹` is, on `O`, a finite exponential sum
`Σ_(u ∈ T₁) Φ₁(u) ψ(u ξ)` with `T₁ ⊆ a⁻¹ O = scaledIntegers F a`. -/
theorem exists_unit_inversion (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ) (η : AdditiveHaarMeasure F.Carrier) (a : F.Carrierˣ)
    (ha : (a : F.Carrier) ∈ (ValuativeRel.valuation F.Carrier).integer)
    (S1 : F.Carrier → ℂ)
    (hper : ∀ ξ ∈ (ValuativeRel.valuation F.Carrier).integer, ∀ δ ∈ scaledIntegers F a⁻¹,
      S1 (ξ + δ) = S1 ξ) :
    ∃ T₁ : Finset F.Carrier, (T₁ : Set F.Carrier) ⊆ scaledIntegers F a ∧
      ∃ Φ₁ : F.Carrier → ℂ, ∀ ξ ∈ (ValuativeRel.valuation F.Carrier).integer,
        ∑ u ∈ T₁, Φ₁ u * ψ.complex (u * ξ) = S1 ξ := by
  classical
  obtain ⟨T₁, hT₁K, hT₁, hcov₁⟩ := exists_finset_addCosetReps (scaledIntegers F a)
    (integerAddSubgroup F) (isCompact_scaledIntegers F a)
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier))
  obtain ⟨R, hRO, hR, hcovR⟩ := exists_finset_addCosetReps (integerAddSubgroup F)
    (scaledIntegers F a⁻¹) (isCompact_integer F) (isOpen_scaledIntegers F a⁻¹)
  have hLbO : ∀ x ∈ scaledIntegers F a⁻¹, x ∈ (ValuativeRel.valuation F.Carrier).integer := by
    intro x hx
    have : x = (a : F.Carrier) * (((a⁻¹ : F.Carrierˣ) : F.Carrier) * x) := by
      rw [Units.val_inv_eq_inv_val]; field_simp
    rw [this]
    exact Subring.mul_mem _ ha hx
  have hcard : (T₁.card : ℂ) ≠ 0 := by
    obtain ⟨t, ht, -⟩ := hcov₁ 0 (scaledIntegers F a).zero_mem
    exact_mod_cast (Finset.card_pos.mpr ⟨t, ht⟩).ne'
  refine ⟨T₁, hT₁K, fun u => (T₁.card : ℂ)⁻¹ * ∑ y ∈ R, S1 y * ψ.complex (-(u * y)), ?_⟩
  intro ξ hξ
  have hswap : ∑ u ∈ T₁, (T₁.card : ℂ)⁻¹ * (∑ y ∈ R, S1 y * ψ.complex (-(u * y))) *
      ψ.complex (u * ξ) =
      (T₁.card : ℂ)⁻¹ * ∑ y ∈ R, S1 y * ∑ u ∈ T₁, ψ.complex (u * (ξ - y)) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
    rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  rw [hswap]
  have hR' : ∀ y ∈ R, ∑ u ∈ T₁, ψ.complex (u * (ξ - y)) =
      if ξ - y ∈ scaledIntegers F a⁻¹ then (T₁.card : ℂ) else 0 := fun y hy =>
    sum_reps_character F ψ hψ η a ha T₁ hT₁K hT₁ hcov₁ _ (Subring.sub_mem _ hξ (hRO hy))
  rw [Finset.sum_congr rfl fun y hy => by rw [hR' y hy]]
  -- the periodic extension by zero
  set Φ : F.Carrier → ℂ := fun z =>
    if z ∈ (ValuativeRel.valuation F.Carrier).integer then S1 z else 0 with hΦ
  have hΦper : ∀ z l, l ∈ scaledIntegers F a⁻¹ → Φ (z + l) = Φ z := by
    intro z l hl
    by_cases hz : z ∈ (ValuativeRel.valuation F.Carrier).integer
    · have hzl : z + l ∈ (ValuativeRel.valuation F.Carrier).integer := add_mem hz (hLbO l hl)
      simp only [hΦ, hz, hzl, ↓reduceIte, hper z hz l hl]
    · have hzl : z + l ∉ (ValuativeRel.valuation F.Carrier).integer := by
        intro h
        apply hz
        have := sub_mem h (hLbO l hl)
        simpa using this
      simp only [hΦ, hz, hzl, ↓reduceIte]
  have hsum := sum_reps_eq (scaledIntegers F a⁻¹) Φ hΦper R hR (fun y hy => by
    have hyO : y ∈ (ValuativeRel.valuation F.Carrier).integer := by
      by_contra h; apply hy; simp [hΦ, h]
    exact hcovR y hyO) ξ
  have hΦξ : Φ ξ = S1 ξ := by simp [hΦ, hξ]
  rw [← hΦξ, ← hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hyO : y ∈ (ValuativeRel.valuation F.Carrier).integer := hRO hy
  have hiff : ξ - y ∈ scaledIntegers F a⁻¹ ↔ y - ξ ∈ scaledIntegers F a⁻¹ := by
    constructor
    · intro h; simpa using neg_mem h
    · intro h; simpa using neg_mem h
  by_cases h : y - ξ ∈ scaledIntegers F a⁻¹
  · simp only [hiff.2 h, h, ↓reduceIte, hΦ, hyO]
    field_simp
  · simp only [(not_congr hiff).2 h, h, ↓reduceIte, mul_zero]

end Canonical

end Langlands.RankinSelberg.HighlyRamified
