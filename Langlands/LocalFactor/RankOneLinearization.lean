import Langlands.LocalFactor.RankOneStabilityHelpers

noncomputable section

open scoped Topology WithZero

namespace Langlands.LocalFactor.RankOneStability

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

open PadicAbelian

theorem valuation_one_add {m : ℕ} (hm : 0 < m) {x : F.Carrier}
    (hx : x ∈ T.additiveLattice (-(m : ℤ))) :
    T.discreteValuation (1 + x) = 1 := by
  have hlt : T.discreteValuation x < T.discreteValuation 1 := by
    apply hx.trans_lt
    simpa only [map_one, ← WithZero.exp_zero] using
      (WithZero.exp_lt_exp.mpr (show -(m : ℤ) < 0 by omega))
  simpa only [add_comm, map_one] using T.discreteValuation.map_add_eq_of_lt_right hlt

/-- The actual unit `1+x` for an element of a positive-depth lattice. -/
def oneAddUnit {m : ℕ} (hm : 0 < m)
    (x : T.additiveLattice (-(m : ℤ))) : F.Carrierˣ :=
  Units.mk0 (1 + x.val) (by
    apply (map_ne_zero T.discreteValuation).mp
    rw [valuation_one_add T hm x.property]
    exact one_ne_zero)

@[simp] theorem oneAddUnit_val {m : ℕ} (hm : 0 < m)
    (x : T.additiveLattice (-(m : ℤ))) :
    (oneAddUnit T hm x : F.Carrier) = 1 + x.val := rfl

theorem oneAddUnit_mem {m : ℕ} (hm : 0 < m)
    (x : T.additiveLattice (-(m : ℤ))) :
    oneAddUnit T hm x ∈ T.principalUnits m := by
  refine ⟨valuation_one_add T hm x.property, ?_⟩
  simpa only [oneAddUnit_val, add_sub_cancel_left] using
    (show T.discreteValuation x.val ≤ WithZero.exp (-(m : ℤ)) from x.property)

/-- The multiplicative character becomes additive after discarding the quadratic error. -/
def deepLatticeCharacter (χ : Character) {a m : ℕ}
    (hχ : T.MultiplicativeTrivialAt χ a) (hm : 0 < m) (hquad : a ≤ 2 * m) :
    AddChar (T.additiveLattice (-(m : ℤ))) ℂ where
  toFun x := (χ (oneAddUnit T hm x) : ℂ)
  map_zero_eq_one' := by
    have h : oneAddUnit T hm (0 : T.additiveLattice (-(m : ℤ))) = 1 := by
      apply Units.ext
      simp
    rw [h, map_one, Units.val_one]
  map_add_eq_mul' x y := by
    let v := oneAddUnit T hm x * oneAddUnit T hm y *
      (oneAddUnit T hm (x + y))⁻¹
    have hv : v ∈ T.principalUnits a := by
      constructor
      · change T.discreteValuation
          ((1 + x.val) * (1 + y.val) * (1 + (x.val + y.val))⁻¹) = 1
        rw [map_mul, map_mul, map_inv₀, valuation_one_add T hm x.property,
          valuation_one_add T hm y.property,
          valuation_one_add T hm (x := x.val + y.val) (add_mem x.property y.property)]
        simp
      · have heq : (v : F.Carrier) - 1 =
            x.val * y.val * (1 + (x.val + y.val))⁻¹ := by
          change (1 + x.val) * (1 + y.val) * (1 + (x.val + y.val))⁻¹ - 1 = _
          have hn := (oneAddUnit T hm (x + y)).ne_zero
          change 1 + (x.val + y.val) ≠ 0 at hn
          field_simp
          ring
        rw [heq, map_mul, map_mul, map_inv₀,
          valuation_one_add T hm (x := x.val + y.val) (add_mem x.property y.property),
          inv_one, mul_one]
        calc
          T.discreteValuation x.val * T.discreteValuation y.val ≤
              WithZero.exp (-(m : ℤ)) * WithZero.exp (-(m : ℤ)) :=
            mul_le_mul' x.property y.property
          _ = WithZero.exp (-(2 * (m : ℤ))) := by
            rw [← WithZero.exp_add]
            congr 1
            ring
          _ ≤ _ := WithZero.exp_le_exp.mpr (by omega)
    have h := congrArg (fun z : ℂˣ => (z : ℂ)) (hχ v hv)
    change ((χ (oneAddUnit T hm x * oneAddUnit T hm y *
      (oneAddUnit T hm (x + y))⁻¹)) : ℂ) = 1 at h
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val] at h
    have hn : (χ (oneAddUnit T hm (x + y)) : ℂ) ≠ 0 := Units.ne_zero _
    exact ((mul_inv_eq_one₀ hn).mp h).symm

theorem deepLatticeCharacter_trivial (χ : Character) {a m : ℕ}
    (hχ : T.MultiplicativeTrivialAt χ a) (hm : 0 < m) (hquad : a ≤ 2 * m)
    (x : T.additiveLattice (-(m : ℤ))) (hx : x.val ∈ T.additiveLattice (-(a : ℤ))) :
    deepLatticeCharacter T χ hχ hm hquad x = 1 := by
  change (χ (oneAddUnit T hm x) : ℂ) = 1
  have hu : oneAddUnit T hm x ∈ T.principalUnits a := by
    refine ⟨valuation_one_add T hm x.property, ?_⟩
    simpa only [oneAddUnit_val, add_sub_cancel_left] using
      (show T.discreteValuation x.val ≤ WithZero.exp (-(a : ℤ)) from hx)
  rw [hχ _ hu, Units.val_one]

/-- A deep character is represented by a parameter on the precise conductor shell. -/
theorem exists_deep_linearization (χ : Character) (ψ : AdditiveCharacter)
    {m : ℕ} (hm : 0 < m) (hma : m < T.multiplicativeConductor χ)
    (hquad : T.multiplicativeConductor χ ≤ 2 * m) :
    letI := T.topology
    ∃ c : F.Carrier, c ≠ 0 ∧
      T.ord c = -((T.multiplicativeConductor χ : ℤ) + T.additiveConductor ψ) ∧
      ∀ x : T.additiveLattice (-(m : ℤ)),
        (χ (oneAddUnit T hm x) : ℂ) = ψ.complex (c * x.val) := by
  let := T.topology
  let a := T.multiplicativeConductor χ
  have hχ := T.multiplicativeConductor_spec χ
  let φ := deepLatticeCharacter T χ hχ hm hquad
  obtain ⟨c, hc⟩ := T.exists_parameter_lattice_character ψ (-(a : ℤ)) (-(m : ℤ)) φ
    (deepLatticeCharacter_trivial T χ hχ hm hquad)
  have hcmem : c ∈ T.additiveLattice (T.additiveConductor ψ + a) := by
    have h := T.mem_additiveLattice_of_forall_complex_mul_eq_one ψ (-(a : ℤ)) c (by
      intro x hx
      have hxm : x ∈ T.additiveLattice (-(m : ℤ)) :=
        T.additiveLattice_mono (by omega) hx
      rw [← hc x hxm]
      exact deepLatticeCharacter_trivial T χ hχ hm hquad ⟨x, hxm⟩ hx)
    simpa only [sub_neg_eq_add] using h
  obtain ⟨v, hv, hχv⟩ := T.exists_nontrivial_below_multiplicativeConductor χ (a - 1) (by
    dsimp [a] at *
    omega)
  have hx : (v : F.Carrier) - 1 ∈ T.additiveLattice (-((a - 1 : ℕ) : ℤ)) := hv.2
  have hxm : (v : F.Carrier) - 1 ∈ T.additiveLattice (-(m : ℤ)) :=
    T.additiveLattice_mono (by dsimp [a] at *; omega) hx
  have hnontriv : ψ.complex (c * ((v : F.Carrier) - 1)) ≠ 1 := by
    rw [← hc _ hxm]
    change (χ (oneAddUnit T hm ⟨(v : F.Carrier) - 1, hxm⟩) : ℂ) ≠ 1
    have heq : oneAddUnit T hm ⟨(v : F.Carrier) - 1, hxm⟩ = v := by
      apply Units.ext
      simp
    rw [heq]
    intro h
    exact hχv (Units.ext h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hnontriv (by simp only [zero_mul, AddChar.map_zero_eq_one])
  have hcnot : c ∉ T.additiveLattice (T.additiveConductor ψ + (a - 1 : ℕ)) := by
    intro h
    apply hnontriv
    apply T.complex_eq_one_of_mem_conductor ψ
    have hh := T.mul_mem_additiveLattice_add h hx
    simpa only [add_neg_cancel_right] using hh
  have hord : T.ord c = -((a : ℤ) + T.additiveConductor ψ) := by
    rw [T.mem_additiveLattice, gauss_valuation_le_exp_iff T hc0] at hcmem hcnot
    dsimp [a] at *
    omega
  refine ⟨c, hc0, hord, ?_⟩
  intro x
  exact hc x.val x.property

end Langlands.LocalFactor.RankOneStability
