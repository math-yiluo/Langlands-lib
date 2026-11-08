import Langlands.LocalFactor.DeligneHenniartNormTrace
import Langlands.LocalFactor.DeligneHenniartApproximateCoset

/-! # The approximate rank-one twist relation (DH81 1.1 and 1.3(i)) -/

noncomputable section

open MeasureTheory

universe u

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

section ApproximateRankOne

variable {p : ℕ} [Fact p.Prime] {G : PadicField.{u} p} (T : G.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter G.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter G.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure G.Carrier _ T.topology (@borel G.Carrier T.topology)

open RankOneStability PadicAbelian
attribute [local instance] Classical.propDecidable

/-- Twisting by a character of smaller conductor does not change the conductor. -/
theorem multiplicativeConductor_mul_of_lt (χ η : Character)
    (hη : T.multiplicativeConductor η < T.multiplicativeConductor χ) :
    T.multiplicativeConductor (χ * η) = T.multiplicativeConductor χ := by
  let := T.topology
  apply le_antisymm
  · rw [← T.multiplicativeTrivialAt_iff_conductor_le]
    intro u hu
    change χ u * η u = 1
    rw [T.multiplicativeConductor_spec χ u hu,
      (T.multiplicativeTrivialAt_iff_conductor_le η _).mpr hη.le u hu, one_mul]
  · by_contra hlt
    push Not at hlt
    set n := max (T.multiplicativeConductor (χ * η)) (T.multiplicativeConductor η)
    have hn : n < T.multiplicativeConductor χ := max_lt hlt hη
    have htriv : T.MultiplicativeTrivialAt χ n := by
      intro u hu
      have h1 : (χ * η) u = 1 :=
        (T.multiplicativeTrivialAt_iff_conductor_le (χ * η) n).mpr (le_max_left _ _) u hu
      have h2 : η u = 1 :=
        (T.multiplicativeTrivialAt_iff_conductor_le η n).mpr (le_max_right _ _) u hu
      change χ u * η u = 1 at h1
      rw [h2, mul_one] at h1
      exact h1
    exact absurd ((T.multiplicativeTrivialAt_iff_conductor_le χ n).mp htriv) (not_le.mpr hn)

/-- A character takes `p`-power roots of unity on principal units of level one. -/
theorem exists_pow_eq_one_of_mem_principalUnits_one (χ : Character) {w : G.Carrierˣ}
    (hw : w ∈ T.principalUnits 1) :
    ∀ N : ℕ, T.multiplicativeConductor χ ≤ N + 1 → (χ w : ℂ) ^ (p ^ N) = 1 := by
  intro N hN
  have h := (T.multiplicativeTrivialAt_iff_conductor_le χ _).mpr hN _
    (T.pow_prime_pow_mem_principalUnits hw N)
  rw [map_pow] at h
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

/-- An additive character takes `p`-power roots of unity. -/
theorem additive_pow_eq_one (ψ : AdditiveCharacter) (b : G.Carrier) {j : ℤ}
    (hb : b ∈ T.additiveLattice (T.additiveConductor ψ + j)) :
    letI := T.topology
    ∀ N : ℕ, j ≤ N → ψ.complex b ^ (p ^ N) = 1 := by
  let := T.topology
  intro N hN
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  apply T.complex_eq_one_of_mem_conductor ψ
  change T.discreteValuation (((p ^ N : ℕ) : G.Carrier) * b) ≤ _
  rw [map_mul]
  have hp : T.discreteValuation ((p ^ N : ℕ) : G.Carrier) ≤ WithZero.exp (-(N : ℤ)) := by
    push_cast
    rw [map_pow]
    calc T.discreteValuation (p : G.Carrier) ^ N ≤ (WithZero.exp (-1)) ^ N :=
          pow_le_pow_left₀ zero_le T.discreteValuation_prime_le N
      _ = WithZero.exp (-(N : ℤ)) := by
          rw [← WithZero.exp_nsmul]
          congr 1
          simp
  calc T.discreteValuation ((p ^ N : ℕ) : G.Carrier) * T.discreteValuation b ≤
        WithZero.exp (-(N : ℤ)) * WithZero.exp (T.additiveConductor ψ + j) :=
        mul_le_mul' hp hb
    _ = WithZero.exp (T.additiveConductor ψ + j - N) := by
        rw [← WithZero.exp_add]
        congr 1
        ring
    _ ≤ WithZero.exp (T.additiveConductor ψ) := WithZero.exp_le_exp.mpr (by omega)

/-- DH81 (1.1.1) for Gauss integrals. Let `d` linearize `χ` at depth `m` on the conductor
shell, and let `b` linearize `η` at depth `k`, where `a = m + k` and `k ≤ m`. For a
principal unit `w = 1 + b/d` of level one, the Gauss integral of `χη` is that of `χ`
times `(χη)(w)⁻¹ η(d)⁻¹ ψ(b)`. -/
theorem gauss_integral_twist_shift (χ η : Character) (ψ : AdditiveCharacter) (μ : LocalHaar)
    (a m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hlevels : a = m + k) (hkm : k ≤ m)
    (d : G.Carrierˣ) (hd : T.ord (d : G.Carrier) = -(T.additiveConductor ψ + a))
    (hlin : letI := T.topology; ∀ h : T.additiveLattice (-(m : ℤ)),
      (χ (oneAddUnit T hm h) : ℂ) = ψ.complex ((d : G.Carrier) * h.val))
    (b : G.Carrier)
    (hlinη : letI := T.topology; ∀ h : T.additiveLattice (-(k : ℤ)),
      (η (oneAddUnit T hk h) : ℂ) = ψ.complex (b * h.val))
    (w : G.Carrierˣ) (hw : (w : G.Carrier) = 1 + b / d) (hw1 : w ∈ T.principalUnits 1) :
    letI := T.topology
    letI : MeasurableSpace G.Carrier := borel G.Carrier
    ∫ x in gaussShell T (T.additiveConductor ψ + a),
        gaussIntegrand T (χ * η) ψ.toAddChar 0 x ∂μ.measure =
      ((χ * η) w : ℂ)⁻¹ * (η d : ℂ)⁻¹ * ψ.complex b *
        ∫ x in gaussShell T (T.additiveConductor ψ + a),
          gaussIntegrand T χ ψ.toAddChar 0 x ∂μ.measure := by
  let := T.topology
  let : MeasurableSpace G.Carrier := borel G.Carrier
  have hd0 : (d : G.Carrier) ≠ 0 := d.ne_zero
  have hvd : T.discreteValuation (d : G.Carrier) = WithZero.exp (T.additiveConductor ψ + a) := by
    rw [gauss_valuation_eq_exp_neg_ord T hd0, hd, neg_neg]
  have hvw : T.discreteValuation (w : G.Carrier) = 1 := hw1.1
  have hw0 : T.ord (w : G.Carrier) = 0 := by
    have hv := hvw
    rw [gauss_valuation_eq_exp_neg_ord T w.ne_zero, ← WithZero.exp_zero] at hv
    have hh := WithZero.exp_injective hv
    omega
  set e : G.Carrierˣ := d * w with he
  have he' : (e : G.Carrier) = d + b := by
    rw [he, Units.val_mul, hw]
    field_simp
  have hdmem : (d : G.Carrier) ∈ T.additiveLattice (T.additiveConductor ψ + a) := by
    change T.discreteValuation (d : G.Carrier) ≤ _
    rw [hvd]
  have hemem : (e : G.Carrier) ∈ T.additiveLattice (T.additiveConductor ψ + a) := by
    change T.discreteValuation (e : G.Carrier) ≤ _
    rw [he, Units.val_mul, map_mul, hvd, hvw, mul_one]
  have hlin' : ∀ h : T.additiveLattice (-(m : ℤ)),
      ((χ * η) (oneAddUnit T hm h) : ℂ) = ψ.complex ((e : G.Carrier) * h.val) := by
    intro h
    have hhk : h.val ∈ T.additiveLattice (-(k : ℤ)) :=
      T.additiveLattice_mono (by omega) h.property
    have hu : oneAddUnit T hm h = oneAddUnit T hk ⟨h.val, hhk⟩ := Units.ext rfl
    change ((χ (oneAddUnit T hm h) * η (oneAddUnit T hm h) : ℂˣ) : ℂ) = _
    rw [Units.val_mul, hlin h, hu, hlinη ⟨h.val, hhk⟩, ← AddChar.map_add_eq_mul, he']
    congr 1
    ring
  rw [gauss_integral_localized T (χ * η) ψ μ a hm (e : G.Carrier) hemem hlin',
    gauss_integral_localized T χ ψ μ a hm (d : G.Carrier) hdmem hlin]
  have hrot := setIntegral_gaussShell_mul_unit T μ w hw0 (T.additiveConductor ψ + a)
    (fun x => if x - (e : G.Carrier) ∈ T.additiveLattice (T.additiveConductor ψ + m)
      then gaussIntegrand T (χ * η) ψ.toAddChar 0 x else 0)
  refine hrot.symm.trans ?_
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (gaussShell_measurableSet T _)
  intro x hx
  dsimp only
  have hiff : (w : G.Carrier) * x - e ∈ T.additiveLattice (T.additiveConductor ψ + m) ↔
      x - d ∈ T.additiveLattice (T.additiveConductor ψ + m) := by
    have heq : (w : G.Carrier) * x - e = (w : G.Carrier) * (x - d) := by
      rw [he, Units.val_mul]
      ring
    rw [heq]
    change T.discreteValuation _ ≤ _ ↔ T.discreteValuation _ ≤ _
    rw [map_mul, hvw, one_mul]
  by_cases h : x - (d : G.Carrier) ∈ T.additiveLattice (T.additiveConductor ψ + m)
  · simp only [hiff.mpr h, h, ↓reduceIte]
    set X : G.Carrierˣ := Units.mk0 x hx.1 with hX
    have hratio : X * d⁻¹ ∈ T.principalUnits k :=
      localized_ratio_mem T ψ a m k hlevels d X hd hx.2 h
    set V := X * d⁻¹ with hV
    have hXV : X = d * V := by rw [hV, mul_comm d, mul_assoc, inv_mul_cancel, mul_one]
    have hval (κ : Character) : characterExtension T κ x = (κ X : ℂ) := by
      simp [characterExtension, hx.1, X]
    have hV1 : (V : G.Carrier) - 1 ∈ T.additiveLattice (-(k : ℤ)) := hratio.2
    have hηV : (η V : ℂ) = ψ.complex (b * ((V : G.Carrier) - 1)) := by
      have hu : oneAddUnit T hk ⟨(V : G.Carrier) - 1, hV1⟩ = V := by
        apply Units.ext
        simp
      rw [← hlinη ⟨(V : G.Carrier) - 1, hV1⟩, hu]
    have hVx : (V : G.Carrier) = x * (d : G.Carrier)⁻¹ := by
      rw [hV, Units.val_mul, Units.val_inv_eq_inv_val]
      rfl
    have hwx : (w : G.Carrier) * x = x + (b + b * ((V : G.Carrier) - 1)) := by
      rw [hw, hVx]
      field_simp
      ring
    rw [gaussIntegrand_zero_apply, gaussIntegrand_zero_apply, characterExtension_unit_mul,
      hval, hval]
    change ((((χ * η) w : ℂˣ) : ℂ) * (((χ * η) X : ℂˣ) : ℂ))⁻¹ *
        ψ.complex ((w : G.Carrier) * x) =
      (((χ * η) w : ℂˣ) : ℂ)⁻¹ * (η d : ℂ)⁻¹ * ψ.complex b *
        ((χ X : ℂ)⁻¹ * ψ.complex x)
    have hχη : (((χ * η) X : ℂˣ) : ℂ) = (χ X : ℂ) * ((η d : ℂ) * (η V : ℂ)) := by
      change ((χ X * η X : ℂˣ) : ℂ) = _
      rw [Units.val_mul, show η X = η d * η V by rw [hXV, map_mul], Units.val_mul]
    rw [hχη, hwx, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← hηV]
    have h1 : (((χ * η) w : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h2 : (χ X : ℂ) ≠ 0 := Units.ne_zero _
    have h3 : (η d : ℂ) ≠ 0 := Units.ne_zero _
    have h4 : (η V : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · simp only [mt hiff.mp h, h, ↓reduceIte, mul_zero]

/-- DH81 Proposition 1.1 and Corollary 1.3(i): let `χ` have conductor `a ≥ 2` and let `d`
(of order `-(n(ψ) + a)`) linearize `χ` at depth `a - ⌊a/2⌋`. For every `η` of conductor
less than `a` and every Haar measure, the epsilon expression of `χη` agrees with
`η(d⁻¹)` times that of `χ` up to a root of unity of `p`-power order. -/
theorem abelianEpsilonExpression_mul_shift (χ η : Character) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (ha : 2 ≤ T.multiplicativeConductor χ)
    (hη : T.multiplicativeConductor η < T.multiplicativeConductor χ)
    (d : G.Carrierˣ)
    (hd : T.ord (d : G.Carrier) = -(T.additiveConductor ψ + T.multiplicativeConductor χ))
    (hm : 0 < T.multiplicativeConductor χ - T.multiplicativeConductor χ / 2)
    (hlin : letI := T.topology;
      ∀ h : T.additiveLattice (-((T.multiplicativeConductor χ -
          T.multiplicativeConductor χ / 2 : ℕ) : ℤ)),
        (χ (oneAddUnit T hm h) : ℂ) = ψ.complex ((d : G.Carrier) * h.val)) :
    ∃ N : ℕ, T.abelianEpsilonExpression (χ * η) ψ μ ^ (p ^ N) =
      ((η d⁻¹ : ℂ) * T.abelianEpsilonExpression χ ψ μ) ^ (p ^ N) := by
  let := T.topology
  let : MeasurableSpace G.Carrier := borel G.Carrier
  set a := T.multiplicativeConductor χ with ha'
  set k := a / 2 with hk'
  set m := a - k with hm'
  have hlevels : a = m + k := by omega
  have hkm : k ≤ m := by omega
  have hk : 0 < k := by omega
  obtain ⟨b, hb, hlinη⟩ : ∃ b : G.Carrier,
      b ∈ T.additiveLattice (T.additiveConductor ψ + ((a : ℤ) - 1)) ∧
      ∀ h : T.additiveLattice (-(k : ℤ)),
        (η (oneAddUnit T hk h) : ℂ) = ψ.complex (b * h.val) := by
    by_cases hηk : T.multiplicativeConductor η ≤ k
    · refine ⟨0, (T.additiveLattice _).zero_mem, fun h => ?_⟩
      rw [(T.multiplicativeTrivialAt_iff_conductor_le η k).mpr hηk _ (oneAddUnit_mem T hk h),
        zero_mul, AddChar.map_zero_eq_one, Units.val_one]
    · push Not at hηk
      obtain ⟨b, hb0, hbord, hblin⟩ := exists_deep_linearization T η ψ hk hηk (by omega)
      refine ⟨b, ?_, hblin⟩
      change T.discreteValuation b ≤ _
      rw [gauss_valuation_eq_exp_neg_ord T hb0, hbord, WithZero.exp_le_exp]
      omega
  have hd0 : (d : G.Carrier) ≠ 0 := d.ne_zero
  have hbd : b / d ∈ T.additiveLattice (-((1 : ℕ) : ℤ)) := by
    change T.discreteValuation (b / d) ≤ _
    rw [div_eq_mul_inv, map_mul, map_inv₀, gauss_valuation_eq_exp_neg_ord T hd0, hd, neg_neg]
    calc T.discreteValuation b * (WithZero.exp (T.additiveConductor ψ + a))⁻¹ ≤
        WithZero.exp (T.additiveConductor ψ + ((a : ℤ) - 1)) *
          (WithZero.exp (T.additiveConductor ψ + a))⁻¹ := mul_le_mul_left hb _
      _ = WithZero.exp (-((1 : ℕ) : ℤ)) := by
        rw [← WithZero.exp_neg, ← WithZero.exp_add]
        congr 1
        push_cast
        ring
  let w := oneAddUnit T one_pos ⟨b / d, hbd⟩
  have hw1 : w ∈ T.principalUnits 1 := oneAddUnit_mem T one_pos _
  have hint := gauss_integral_twist_shift T χ η ψ μ a m k hm hk hlevels hkm d hd hlin b hlinη
    w rfl hw1
  have hcond : T.multiplicativeConductor (χ * η) = a := multiplicativeConductor_mul_of_lt T χ η hη
  have ha0 : a ≠ 0 := by omega
  have hE : T.abelianEpsilonExpression (χ * η) ψ μ =
      ((χ * η) w : ℂ)⁻¹ * (η d : ℂ)⁻¹ * ψ.complex b * T.abelianEpsilonExpression χ ψ μ := by
    rw [← PadicAbelian.deligneConstant_eq_abelianEpsilonExpression,
      ← PadicAbelian.deligneConstant_eq_abelianEpsilonExpression]
    dsimp only [PadicAbelian.deligneConstant, PadicAbelian.epsilon, PadicAbelian.epsilonAt]
    rw [hcond, ite_eq_right ha0, ite_eq_right ha0]
    exact hint
  have hA : (((χ * η) w : ℂˣ) : ℂ) ^ (p ^ a) = 1 :=
    exists_pow_eq_one_of_mem_principalUnits_one T (χ * η) hw1 a (by omega)
  have hC : ψ.complex b ^ (p ^ a) = 1 := additive_pow_eq_one T ψ b hb a (by omega)
  refine ⟨a, ?_⟩
  rw [hE, map_inv η d, Units.val_inv_eq_inv_val, mul_pow, mul_pow, mul_pow, inv_pow, hA, hC,
    mul_pow]
  ring

/-- The approximate twist relation at any element congruent to the linearizer modulo the
principal units of level one. -/
theorem abelianEpsilonExpression_mul_shift_of_comparison (χ η : Character)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (ha : 2 ≤ T.multiplicativeConductor χ)
    (hη : T.multiplicativeConductor η < T.multiplicativeConductor χ)
    (d : G.Carrierˣ)
    (hd : T.ord (d : G.Carrier) = -(T.additiveConductor ψ + T.multiplicativeConductor χ))
    (hm : 0 < T.multiplicativeConductor χ - T.multiplicativeConductor χ / 2)
    (hlin : letI := T.topology;
      ∀ h : T.additiveLattice (-((T.multiplicativeConductor χ -
          T.multiplicativeConductor χ / 2 : ℕ) : ℤ)),
        (χ (oneAddUnit T hm h) : ℂ) = ψ.complex ((d : G.Carrier) * h.val))
    (c : G.Carrierˣ) (hcd : c * d⁻¹ ∈ T.principalUnits 1) :
    ∃ N : ℕ, T.abelianEpsilonExpression (χ * η) ψ μ ^ (p ^ N) =
      ((η c⁻¹ : ℂ) * T.abelianEpsilonExpression χ ψ μ) ^ (p ^ N) := by
  let := T.topology
  obtain ⟨N, hN⟩ := abelianEpsilonExpression_mul_shift T χ η ψ μ ha hη d hd hm hlin
  set M := T.multiplicativeConductor η with hM
  have hdc : d * c⁻¹ ∈ T.principalUnits 1 := by
    have := (T.principalUnits 1).inv_mem hcd
    rwa [mul_inv_rev, inv_inv] at this
  have h1 : ((η (d * c⁻¹) : ℂˣ) : ℂ) ^ (p ^ (N + M)) = 1 :=
    exists_pow_eq_one_of_mem_principalUnits_one T η hdc (N + M) (by omega)
  have hc : (η c⁻¹ : ℂ) = (η d⁻¹ : ℂ) * (η (d * c⁻¹) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨N + M, ?_⟩
  rw [hc, show (η d⁻¹ : ℂ) * (η (d * c⁻¹) : ℂ) * T.abelianEpsilonExpression χ ψ μ =
      ((η d⁻¹ : ℂ) * T.abelianEpsilonExpression χ ψ μ) * (η (d * c⁻¹) : ℂ) by ring,
    mul_pow, h1, mul_one, pow_add, pow_mul, pow_mul, hN]

/-- The approximate rank-one twist relation of DH81 Corollary 1.3(i) at `γ`: for every `η` of
conductor less than that of `χ` and every Haar measure, the epsilon expression of `χη`
agrees with `η(γ)` times that of `χ` up to a root of unity of `p`-power order. -/
def ApproximateTwistWitness (χ : Character) (ψ : AdditiveCharacter) (γ : G.Carrierˣ) :
    Prop :=
  ∀ η : Character, T.multiplicativeConductor η < T.multiplicativeConductor χ →
    ∀ μ : LocalHaar, ∃ N : ℕ, T.abelianEpsilonExpression (χ * η) ψ μ ^ (p ^ N) =
      ((η γ : ℂ) * T.abelianEpsilonExpression χ ψ μ) ^ (p ^ N)

/-- The inverse of any element congruent to a linearizer modulo `U^1` is an approximate
twist witness. -/
theorem approximateTwistWitness_of_comparison (χ : Character) (ψ : AdditiveCharacter)
    (ha : 2 ≤ T.multiplicativeConductor χ) (d : G.Carrierˣ)
    (hd : T.ord (d : G.Carrier) = -(T.additiveConductor ψ + T.multiplicativeConductor χ))
    (hm : 0 < T.multiplicativeConductor χ - T.multiplicativeConductor χ / 2)
    (hlin : letI := T.topology;
      ∀ h : T.additiveLattice (-((T.multiplicativeConductor χ -
          T.multiplicativeConductor χ / 2 : ℕ) : ℤ)),
        (χ (oneAddUnit T hm h) : ℂ) = ψ.complex ((d : G.Carrier) * h.val))
    (c : G.Carrierˣ) (hcd : c * d⁻¹ ∈ T.principalUnits 1) :
    ApproximateTwistWitness T χ ψ c⁻¹ := fun η hη μ =>
  abelianEpsilonExpression_mul_shift_of_comparison T χ η ψ μ ha hη d hd hm hlin c hcd

/-- A wildly ramified character has an approximate twist witness of order `a(χ) + n(ψ)`:
the inverse of a linearizer. -/
theorem exists_approximateTwistWitness (χ : Character) (ψ : AdditiveCharacter)
    (ha : 2 ≤ T.multiplicativeConductor χ) :
    ∃ γ : G.Carrierˣ, T.ord (γ : G.Carrier) =
        (T.multiplicativeConductor χ : ℤ) + T.additiveConductor ψ ∧
      ApproximateTwistWitness T χ ψ γ := by
  let := T.topology
  have hm : 0 < T.multiplicativeConductor χ - T.multiplicativeConductor χ / 2 := by omega
  obtain ⟨c, hc0, hcord, hlin⟩ := exists_deep_linearization T χ ψ hm (by omega) (by omega)
  let d : G.Carrierˣ := Units.mk0 c hc0
  have hd : T.ord (d : G.Carrier) =
      -(T.additiveConductor ψ + T.multiplicativeConductor χ) := by
    change T.ord c = _
    rw [hcord]
    ring
  refine ⟨d⁻¹, ?_, fun η hη μ => abelianEpsilonExpression_mul_shift T χ η ψ μ ha hη d hd hm hlin⟩
  rw [Units.val_inv_eq_inv_val, T.ord_inv, hd]
  ring

end ApproximateRankOne

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
