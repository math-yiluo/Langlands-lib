import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier
import Langlands.HarmonicAnalysis.PadicLatticeFourierProof
import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual

/-!
# The twisted principal test of Jacquet–Shalika §2.5 and its Fourier support

For a quasicharacter `χ` of conductor exponent `k` and a level `j ≥ 1` with
`k ≤ 2j`, the function `Φ(y) = χ(det y)⁻¹` on `1 + ϖ^j M(O)`, extended by zero,
is a Schwartz–Bruhat test on all square matrices. Translating by
`a ∈ ϖ^j M(O)` multiplies it by `χ(1 + tr a)⁻¹`, because
`det(1 + Y + a) ≡ det(1 + Y)(1 + tr a)` modulo `ϖ^(2j)`. Hence its plus-sign
Fourier transform `Φ^` satisfies `ψ(⟨a, x⟩) = χ(1 + tr a)` wherever it does not
vanish. For `ψ` of conductor exponent `0` and `j ≤ k - 1` this forces
`|x₀₀| = q^k` and `x ∈ x₀₀ (1 + ϖ^(k-j) M(O))` on the support of `Φ^`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators WithZero

namespace Langlands.RankinSelberg.UniformTwist

open HarmonicAnalysis

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance uniformRankOneTwistTestTopologicalSpace : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance uniformRankOneTwistTestValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance uniformRankOneTwistTestIsNonarchimedeanLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance uniformRankOneTwistTestT2Space : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance uniformRankOneTwistTestMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance uniformRankOneTwistTestBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

section Valuation

theorem mul_mem_lattice {a b : ℤ} {x y : F.Carrier} (hx : x ∈ 𝓛 a) (hy : y ∈ 𝓛 b) :
    x * y ∈ 𝓛 (a + b) := by
  rw [PadicField.TopologicalData.mem_additiveLattice] at hx hy ⊢
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

/-- An element of `ϖ^j O` with `j ≥ 1` has valuation strictly below one. -/
theorem valuation_lt_one_of_mem {j : ℤ} (hj : j < 0) {t : F.Carrier} (ht : t ∈ 𝓛 j) :
    (T).discreteValuation t < 1 :=
  lt_of_le_of_lt ht (by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr hj)

/-- `1 + t` with `t ∈ ϖ^j O`, `j ≥ 1`, is a valuation unit. -/
theorem valuation_one_add {j : ℤ} (hj : j < 0) {t : F.Carrier} (ht : t ∈ 𝓛 j) :
    (T).discreteValuation (1 + t) = 1 :=
  Valuation.map_one_add_of_lt _ (valuation_lt_one_of_mem F hj ht)

/-- A unit congruent to one modulo `ϖ^j O`, `j ≥ 1`, lies in the principal units of
every level `k ≤ j`. -/
theorem mem_principalUnits_of_sub_one_mem {j : ℕ} (hj : 0 < j) {k : ℕ} (hkj : k ≤ j)
    (u : F.Carrierˣ) (hu : (u : F.Carrier) - 1 ∈ 𝓛 (-(j : ℤ))) :
    u ∈ (T).principalUnits k := by
  refine ⟨?_, hu.trans (WithZero.exp_le_exp.mpr (by omega))⟩
  have h := valuation_one_add F (by omega : -(j : ℤ) < 0) hu
  rwa [add_sub_cancel] at h

/-- Division by a valuation unit preserves every lattice. -/
theorem div_mem_lattice_of_valuation_eq_one {a : ℤ} {x w : F.Carrier} (hx : x ∈ 𝓛 a)
    (hw : (T).discreteValuation w = 1) : x / w ∈ 𝓛 a := by
  rw [PadicField.TopologicalData.mem_additiveLattice, map_div₀, hw, div_one]
  exact hx

/-- An element of valuation `exp k` exactly. -/
theorem valuation_eq_exp_of_le_of_not_le {k : ℤ} {x : F.Carrier} (h₁ : x ∈ 𝓛 k)
    (h₂ : x ∉ 𝓛 (k - 1)) : (T).discreteValuation x = WithZero.exp k := by
  rw [PadicField.TopologicalData.mem_additiveLattice] at h₁ h₂
  have hx0 : (T).discreteValuation x ≠ 0 := by
    intro h0
    apply h₂
    rw [h0]
    exact zero_le
  rw [← WithZero.exp_log hx0] at h₁ h₂ ⊢
  rw [WithZero.exp_le_exp] at h₁ h₂
  rw [WithZero.exp_inj]
  omega

end Valuation

section MatrixLattice

variable {n : ℕ}

/-- The additive subgroup of square matrices all of whose entries lie in `𝓛 i`. -/
def matrixLattice (n : ℕ) (i : ℤ) :
    AddSubgroup (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) where
  carrier := {a | ∀ r c, a r c ∈ 𝓛 i}
  add_mem' ha hb r c := add_mem (ha r c) (hb r c)
  zero_mem' _ _ := zero_mem _
  neg_mem' ha r c := neg_mem (ha r c)

theorem mem_matrixLattice {i : ℤ} {a : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier} :
    a ∈ matrixLattice F n i ↔ ∀ r c, a r c ∈ 𝓛 i := Iff.rfl

theorem matrixLattice_mono {i i' : ℤ} (h : i ≤ i') :
    matrixLattice F n i ≤ matrixLattice F n i' :=
  fun _ ha r c => (T).additiveLattice_mono h (ha r c)

theorem trace_mem_lattice {i : ℤ} {a : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier}
    (ha : a ∈ matrixLattice F n i) : a.trace ∈ 𝓛 i :=
  sum_mem fun r _ => ha r r

/-- The entrywise lattice as an entrywise lattice coset centred at zero. -/
theorem matrixLattice_eq_coset (i : ℤ) :
    (matrixLattice F n i : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) =
      rectangularLatticeCoset F T (fun _ _ => i) 0 := by
  ext a
  rw [mem_rectangularLatticeCoset]
  simp only [Matrix.zero_apply, sub_zero]
  rfl

theorem isOpen_matrixLattice (i : ℤ) :
    IsOpen (matrixLattice F n i : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) := by
  rw [matrixLattice_eq_coset]
  exact (isClopen_rectangularLatticeCoset F T _ _).isOpen

/-- First-order expansion of the determinant: for `Z ∈ ϖ^j M(O)`,
`det(1 + Z) ≡ 1 + tr Z` modulo `ϖ^(2j)`. -/
theorem det_one_add_sub_trace_mem {j : ℕ} {Z : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier}
    (hZ : Z ∈ matrixLattice F n (-(j : ℤ))) :
    (1 + Z).det - 1 - Z.trace ∈ 𝓛 (-(2 * j : ℕ)) := by
  classical
  set O := (T).Integers
  set ϖ := (T).uniformizer
  have hϖv : (T).discreteValuation ϖ = WithZero.exp (-1) :=
    (T).discreteValuation_uniformizer
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖv
    exact WithZero.exp_ne_zero hϖv.symm
  have hϖO : ϖ ∈ O := by
    rw [(T).mem_integers_iff_discreteValuation_le_one, hϖv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have hM : ∀ a b, Z a b / ϖ ^ j ∈ O := by
    intro a b
    have h := ((T).mem_additiveLattice_iff_div_mem_integers (-(j : ℤ)) (Z a b)).1 (hZ a b)
    simpa only [neg_neg, zpow_natCast] using h
  let r : O := ⟨ϖ ^ j, pow_mem hϖO j⟩
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) O := fun a b => ⟨Z a b / ϖ ^ j, hM a b⟩
  have hZM : Z = O.subtype.mapMatrix (r • M) := by
    ext a b
    change Z a b = ((r * M a b : O) : F.Carrier)
    simp only [Subring.coe_mul, r, M]
    field_simp
  have hdet := Matrix.det_one_add_smul r M
  set e : O := (Matrix.det (1 + (Polynomial.X : Polynomial O) •
    M.map Polynomial.C)).divX.divX.eval r
  have h1 : (1 + Z).det = O.subtype (Matrix.det (1 + r • M)) := by
    rw [RingHom.map_det, map_add, map_one, ← hZM]
  have h2 : Z.trace = O.subtype (M.trace * r) := by
    rw [hZM, Matrix.trace, Matrix.trace, map_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.diag_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, map_mul]
    ring
  rw [h1, hdet, h2]
  simp only [map_add, map_one, map_mul, map_pow, Subring.coe_subtype]
  have heq : 1 + (M.trace : F.Carrier) * (r : F.Carrier) + (e : F.Carrier) * (r : F.Carrier) ^ 2 -
      1 - (M.trace : F.Carrier) * (r : F.Carrier) = (e : F.Carrier) * ϖ ^ (2 * j) := by
    simp only [r, pow_mul']
    ring
  rw [heq]
  have he : (e : F.Carrier) ∈ 𝓛 0 := ((T).mem_additiveLattice_zero _).2 e.property
  have hp : ϖ ^ (2 * j) ∈ 𝓛 (-(2 * j : ℕ)) := by
    rw [PadicField.TopologicalData.mem_additiveLattice, map_pow, hϖv, ← WithZero.exp_nsmul]
    exact le_of_eq (by congr 1; push_cast; ring)
  simpa only [zero_add] using mul_mem_lattice F he hp

/-- The determinant of `1 + Y + a` against `det(1 + Y)(1 + tr a)`, modulo `ϖ^(2j)`. -/
theorem det_add_sub_det_mul_mem {j : ℕ}
    {Y a : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier}
    (hY : Y ∈ matrixLattice F n (-(j : ℤ))) (ha : a ∈ matrixLattice F n (-(j : ℤ))) :
    (1 + Y + a).det - (1 + Y).det * (1 + a.trace) ∈ 𝓛 (-(2 * j : ℕ)) := by
  have e₁ := det_one_add_sub_trace_mem F (add_mem hY ha)
  have e₂ := det_one_add_sub_trace_mem F hY
  have hYa : Y.trace * a.trace ∈ 𝓛 (-(2 * j : ℕ)) := by
    have := mul_mem_lattice F (trace_mem_lattice F hY) (trace_mem_lattice F ha)
    convert this using 2
    push_cast
    ring
  have hea : ((1 + Y).det - 1 - Y.trace) * a.trace ∈ 𝓛 (-(2 * j : ℕ)) := by
    have := mul_mem_lattice F e₂ (trace_mem_lattice F ha)
    exact (T).additiveLattice_mono (by push_cast; omega) this
  have key : (1 + Y + a).det - (1 + Y).det * (1 + a.trace) =
      ((1 + (Y + a)).det - 1 - (Y + a).trace) - ((1 + Y).det - 1 - Y.trace) -
        Y.trace * a.trace - ((1 + Y).det - 1 - Y.trace) * a.trace := by
    rw [Matrix.trace_add, add_assoc]
    ring
  rw [key]
  exact sub_mem (sub_mem (sub_mem e₁ e₂) hYa) hea

/-- Elements of the principal congruence set have unit determinant congruent to one. -/
theorem det_one_add_sub_one_mem {j : ℕ} (hj : 0 < j)
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier}
    (hY : Y ∈ matrixLattice F n (-(j : ℤ))) :
    (1 + Y).det - 1 ∈ 𝓛 (-(j : ℤ)) := by
  have h := det_one_add_sub_trace_mem F hY
  have h' : (1 + Y).det - 1 - Y.trace ∈ 𝓛 (-(j : ℤ)) :=
    (T).additiveLattice_mono (by push_cast; omega) h
  have := add_mem h' (trace_mem_lattice F hY)
  simpa only [sub_add_cancel] using this

theorem valuation_det_one_add {j : ℕ} (hj : 0 < j)
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier}
    (hY : Y ∈ matrixLattice F n (-(j : ℤ))) :
    (T).discreteValuation (1 + Y).det = 1 := by
  have h := valuation_one_add F (by omega : -(j : ℤ) < 0) (det_one_add_sub_one_mem F hj hY)
  rwa [add_sub_cancel] at h

end MatrixLattice

section Test

variable {n : ℕ}

/-- The principal congruence set `1 + ϖ^j M(O)` inside all square matrices. -/
def principalSet (n j : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  {y | y - 1 ∈ matrixLattice F n (-(j : ℤ))}

theorem principalSet_eq_coset (j : ℕ) :
    principalSet F n j = rectangularLatticeCoset F T (fun _ _ => -(j : ℤ)) 1 := by
  ext y
  rw [mem_rectangularLatticeCoset]
  rfl

theorem isCompact_principalSet (j : ℕ) : IsCompact (principalSet F n j) := by
  rw [principalSet_eq_coset]
  exact isCompact_rectangularLatticeCoset F T _ _

/-- `χ(det y)⁻¹` on invertible matrices, and zero on singular ones. -/
def inverseDetTwist (χ : Quasicharacter F.Carrier)
    (y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) : ℂ :=
  by classical exact if h : y.det = 0 then 0 else (((χ (Units.mk0 y.det h))⁻¹ : ℂˣ) : ℂ)

theorem inverseDetTwist_of_ne (χ : Quasicharacter F.Carrier)
    {y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier} (h : y.det ≠ 0) :
    inverseDetTwist F χ y = (((χ (Units.mk0 y.det h))⁻¹ : ℂˣ) : ℂ) := by
  unfold inverseDetTwist
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- The twisted principal function `1_{1 + ϖ^j M(O)}(y) χ(det y)⁻¹`. -/
def twistedPrincipalFun (χ : Quasicharacter F.Carrier) (j : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ :=
  (principalSet F n j).indicator (inverseDetTwist F χ)

/-- Translation by `a ∈ ϖ^j M(O)` multiplies the twisted principal function by
`χ(1 + tr a)⁻¹`, provided `a(χ) ≤ 2j`. -/
theorem twistedPrincipalFun_add (χ : Quasicharacter F.Carrier) {j : ℕ} (hj : 0 < j)
    (hk : (T).multiplicativeConductor χ ≤ 2 * j)
    (y a : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)
    (ha : a ∈ matrixLattice F n (-(j : ℤ))) (u : F.Carrierˣ)
    (hu : (u : F.Carrier) = 1 + a.trace) :
    twistedPrincipalFun F χ j (y + a) =
      (((χ u)⁻¹ : ℂˣ) : ℂ) * twistedPrincipalFun F χ j y := by
  by_cases hy : y ∈ principalSet F n j
  · have hya : y + a ∈ principalSet F n j := by
      show y + a - 1 ∈ matrixLattice F n (-(j : ℤ))
      rw [add_sub_right_comm]
      exact add_mem hy ha
    set Y := y - 1 with hYdef
    have hyY : y = 1 + Y := by rw [hYdef, add_sub_cancel]
    have hvy : (T).discreteValuation y.det = 1 := by
      rw [hyY]
      exact valuation_det_one_add F hj hy
    have hvya : (T).discreteValuation (y + a).det = 1 := by
      have h := valuation_det_one_add F hj (show y + a - 1 ∈ matrixLattice F n (-(j : ℤ)) from hya)
      rwa [add_sub_cancel] at h
    have hy0 : y.det ≠ 0 := by
      intro h; rw [h, map_zero] at hvy; exact zero_ne_one hvy
    have hya0 : (y + a).det ≠ 0 := by
      intro h; rw [h, map_zero] at hvya; exact zero_ne_one hvya
    have hvu : (T).discreteValuation (u : F.Carrier) = 1 := by
      rw [hu]
      exact valuation_one_add F (by omega : -(j : ℤ) < 0) (trace_mem_lattice F ha)
    rw [twistedPrincipalFun, Set.indicator_of_mem hya, Set.indicator_of_mem hy,
      inverseDetTwist_of_ne F χ hya0, inverseDetTwist_of_ne F χ hy0]
    -- the ratio `det(y + a) / (det y · u)` is a principal unit of level `2j`
    set ρ : F.Carrierˣ := Units.mk0 (y + a).det hya0 * (Units.mk0 y.det hy0 * u)⁻¹ with hρ
    have hρ1 : ((ρ : F.Carrierˣ) : F.Carrier) - 1 ∈ 𝓛 (-(2 * j : ℕ)) := by
      have hw : (T).discreteValuation (y.det * u) = 1 := by rw [map_mul, hvy, hvu, one_mul]
      have hw0 : y.det * (u : F.Carrier) ≠ 0 := mul_ne_zero hy0 u.ne_zero
      have hexp : ((ρ : F.Carrierˣ) : F.Carrier) - 1 =
          ((1 + Y + a).det - (1 + Y).det * (1 + a.trace)) / (y.det * u) := by
        rw [hρ, ← hyY, ← hu]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp
      rw [hexp]
      exact div_mem_lattice_of_valuation_eq_one F (det_add_sub_det_mul_mem F hy ha) hw
    have hρU : ρ ∈ (T).principalUnits ((T).multiplicativeConductor χ) :=
      mem_principalUnits_of_sub_one_mem F (by omega) hk ρ hρ1
    have hχρ : χ ρ = 1 := (T).multiplicativeConductor_spec χ ρ hρU
    have hsplit : Units.mk0 (y + a).det hya0 = ρ * (Units.mk0 y.det hy0 * u) := by
      rw [hρ, inv_mul_cancel_right]
    rw [hsplit, map_mul, hχρ, one_mul, map_mul, mul_inv, Units.val_mul, mul_comm]
  · have hya : y + a ∉ principalSet F n j := by
      intro h
      apply hy
      show y - 1 ∈ matrixLattice F n (-(j : ℤ))
      have := sub_mem (show y + a - 1 ∈ matrixLattice F n (-(j : ℤ)) from h) ha
      rwa [add_sub_right_comm, add_sub_cancel_right] at this
    rw [twistedPrincipalFun, Set.indicator_of_notMem hya, Set.indicator_of_notMem hy,
      mul_zero]

/-- The canonical level `j = max 1 ⌈k/2⌉` attached to a conductor exponent `k`. -/
def twistLevel (k : ℕ) : ℕ := max 1 ((k + 1) / 2)

theorem twistLevel_pos (k : ℕ) : 0 < twistLevel k := lt_of_lt_of_le one_pos (le_max_left _ _)

theorem le_two_mul_twistLevel (k : ℕ) : k ≤ 2 * twistLevel k := by
  unfold twistLevel; omega

theorem twistLevel_eq {k : ℕ} (hk : 1 ≤ k) : twistLevel k = (k + 1) / 2 := by
  unfold twistLevel; omega

theorem isLocallyConstant_twistedPrincipalFun (χ : Quasicharacter F.Carrier) {j : ℕ}
    (hj : 0 < j) (hk : (T).multiplicativeConductor χ ≤ 2 * j) :
    IsLocallyConstant (twistedPrincipalFun F χ j (n := n)) := by
  set k := (T).multiplicativeConductor χ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hU : {y | y - x ∈ matrixLattice F n (-((j + k : ℕ) : ℤ))} ∈ nhds x := by
    apply ((isOpen_matrixLattice F _).preimage (continuous_id.sub continuous_const)).mem_nhds
    show x - x ∈ matrixLattice F n (-((j + k : ℕ) : ℤ))
    rw [sub_self]
    exact (matrixLattice F n _).zero_mem
  filter_upwards [hU] with y hy
  have ha : y - x ∈ matrixLattice F n (-(j : ℤ)) :=
    matrixLattice_mono F (by push_cast; omega) hy
  have htr : (y - x).trace ∈ 𝓛 (-((j + k : ℕ) : ℤ)) := trace_mem_lattice F hy
  have hv := valuation_one_add F (by push_cast; omega : -((j + k : ℕ) : ℤ) < 0) htr
  have h0 : 1 + (y - x).trace ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact zero_ne_one hv
  set u := Units.mk0 (1 + (y - x).trace) h0
  have hu : u ∈ (T).principalUnits k :=
    mem_principalUnits_of_sub_one_mem F (by omega : 0 < j + k) (by omega) u
      (by simpa only [u, Units.val_mk0, add_sub_cancel_left] using htr)
  have h := twistedPrincipalFun_add F χ hj hk x (y - x) ha u (by rw [Units.val_mk0])
  rw [add_sub_cancel] at h
  rw [h, (T).multiplicativeConductor_spec χ u hu, inv_one, Units.val_one, one_mul]

theorem hasCompactSupport_twistedPrincipalFun (χ : Quasicharacter F.Carrier) (j : ℕ) :
    HasCompactSupport (twistedPrincipalFun F χ j (n := n)) := by
  apply HasCompactSupport.intro (isCompact_principalSet F j)
  intro y hy
  exact Set.indicator_of_notMem hy _

/-- The Jacquet–Shalika §2.5 test `1_{1 + ϖ^j M(O)} · χ⁻¹(det)` at the level
`j = twistLevel a(χ)`, as a Schwartz–Bruhat function on all square matrices. -/
def twistedPrincipalTest (n : ℕ) (χ : Quasicharacter F.Carrier) :
    GodementJacquet.MatrixTestFunction n F.Carrier :=
  ⟨twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ)),
    isLocallyConstant_twistedPrincipalFun F χ (twistLevel_pos _)
      (le_two_mul_twistLevel _),
    hasCompactSupport_twistedPrincipalFun F χ _⟩

@[simp] theorem twistedPrincipalTest_apply (χ : Quasicharacter F.Carrier)
    (y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    twistedPrincipalTest F n χ y =
      twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ)) y := rfl

end Test

section Fourier

variable {n : ℕ}

local instance uniformRankOneTwistTestSecondCountableTopology : SecondCountableTopology F.Carrier := (T).secondCountableTopology

local instance instMeasurableAddMatrix (r s : ℕ) :
    MeasurableAdd (Matrix (Fin r) (Fin s) F.Carrier) :=
  inferInstanceAs (MeasurableAdd (Fin r → Fin s → F.Carrier))

theorem rectangularPairing_add_left (a y x : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    rectangularPairing (a + y) x = rectangularPairing a x + rectangularPairing y x := by
  unfold rectangularPairing
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem rectangularPairing_single (r c : Fin (n + 1)) (t : F.Carrier)
    (x : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    rectangularPairing (Matrix.single r c t) x = t * x r c := by
  unfold rectangularPairing
  rw [Finset.sum_eq_single r, Finset.sum_eq_single c]
  · rw [Matrix.single_apply_same]
  · intro b _ hb
    rw [Matrix.single_apply_of_col_ne r r (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ c) h
  · intro b _ hb
    exact Finset.sum_eq_zero fun d _ => by
      rw [Matrix.single_apply_of_row_ne (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ r) h

theorem single_mem_matrixLattice {i : ℤ} (r c : Fin (n + 1)) {t : F.Carrier} (ht : t ∈ 𝓛 i) :
    Matrix.single r c t ∈ matrixLattice F n i := fun a b => by
  rw [Matrix.single_apply]
  split_ifs
  · exact ht
  · exact zero_mem _

/-- Translation invariance of the Fourier integral of the twisted principal function:
for `a ∈ ϖ^j M(O)` and `u = 1 + tr a`, `Φ^(x) = χ(u)⁻¹ ψ(⟨a, x⟩) Φ^(x)`. -/
theorem fourierIntegral_twistedPrincipalFun_eq (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier) {j : ℕ} (hj : 0 < j)
    (hk : (T).multiplicativeConductor χ ≤ 2 * j)
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) (ha : a ∈ matrixLattice F n (-(j : ℤ)))
    (u : F.Carrierˣ) (hu : (u : F.Carrier) = 1 + a.trace)
    (x : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    rectangularFourierIntegral ψ ν (twistedPrincipalFun F χ j) x =
      (((χ u)⁻¹ : ℂˣ) : ℂ) * ψ.complex (rectangularPairing a x) *
        rectangularFourierIntegral ψ ν (twistedPrincipalFun F χ j) x := by
  unfold rectangularFourierIntegral
  conv_lhs =>
    rw [← integral_add_left_eq_self
      (fun y => twistedPrincipalFun F χ j y * ψ.complex (rectangularPairing y x)) a]
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [add_comm a y, twistedPrincipalFun_add F χ hj hk y a ha u hu, add_comm y a,
    rectangularPairing_add_left, AddChar.map_add_eq_mul]
  ring

/-- Where the Fourier integral does not vanish, `ψ(⟨a, x⟩) = χ(1 + tr a)`. -/
theorem character_eq_of_fourierIntegral_ne_zero (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier) {j : ℕ} (hj : 0 < j)
    (hk : (T).multiplicativeConductor χ ≤ 2 * j)
    {x : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier}
    (hx : rectangularFourierIntegral ψ ν (twistedPrincipalFun F χ j) x ≠ 0)
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) (ha : a ∈ matrixLattice F n (-(j : ℤ)))
    (u : F.Carrierˣ) (hu : (u : F.Carrier) = 1 + a.trace) :
    ψ.complex (rectangularPairing a x) = ((χ u : ℂˣ) : ℂ) := by
  have h := fourierIntegral_twistedPrincipalFun_eq F ψ ν χ hj hk a ha u hu x
  have h1 : (((χ u)⁻¹ : ℂˣ) : ℂ) * ψ.complex (rectangularPairing a x) = 1 :=
    mul_right_cancel₀ hx (by rw [one_mul]; exact h.symm)
  calc ψ.complex (rectangularPairing a x)
      = ((χ u : ℂˣ) : ℂ) * ((((χ u)⁻¹ : ℂˣ) : ℂ) * ψ.complex (rectangularPairing a x)) := by
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    _ = ((χ u : ℂˣ) : ℂ) := by rw [h1, mul_one]

/-- The unit `1 + t` for `t ∈ ϖ^j O`, `j ≥ 1`. -/
def onePlusUnit {j : ℕ} (hj : 0 < j) (t : F.Carrier) (ht : t ∈ 𝓛 (-(j : ℤ))) : F.Carrierˣ :=
  Units.mk0 (1 + t) (by
    intro h
    have hv := valuation_one_add F (by omega : -(j : ℤ) < 0) ht
    rw [h, map_zero] at hv
    exact zero_ne_one hv)

@[simp] theorem onePlusUnit_val {j : ℕ} (hj : 0 < j) (t : F.Carrier) (ht : t ∈ 𝓛 (-(j : ℤ))) :
    (onePlusUnit F hj t ht : F.Carrier) = 1 + t := rfl

/-- Entry form of `character_eq_of_fourierIntegral_ne_zero`, with `a` a matrix unit. -/
theorem entry_character_eq (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier) {j : ℕ} (hj : 0 < j)
    (hk : (T).multiplicativeConductor χ ≤ 2 * j)
    {x : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier}
    (hx : rectangularFourierIntegral ψ ν (twistedPrincipalFun F χ j) x ≠ 0)
    (r c : Fin (n + 1)) (t : F.Carrier) (ht : t ∈ 𝓛 (-(j : ℤ))) :
    (ψ (t * x r c) : ℂ) =
      if r = c then ((χ (onePlusUnit F hj t ht) : ℂˣ) : ℂ) else 1 := by
  split_ifs with hrc
  · subst hrc
    have h := character_eq_of_fourierIntegral_ne_zero F ψ ν χ hj hk hx (Matrix.single r r t)
      (single_mem_matrixLattice F r r ht) (onePlusUnit F hj t ht)
      (by rw [onePlusUnit_val, Matrix.trace_single_eq_same])
    rwa [rectangularPairing_single, UnitaryAdditiveCharacter.complex_apply] at h
  · have h := character_eq_of_fourierIntegral_ne_zero F ψ ν χ hj hk hx (Matrix.single r c t)
      (single_mem_matrixLattice F r c ht) 1
      (by rw [Matrix.trace_single_eq_of_ne r c t hrc, add_zero, Units.val_one])
    rwa [rectangularPairing_single, UnitaryAdditiveCharacter.complex_apply, map_one,
      Units.val_one] at h

/-- Support of the Fourier integral of the twisted principal function, for `ψ` of
conductor exponent `0` and `1 ≤ j < a(χ) ≤ 2j`: on its support, `|x₀₀| = q^(a(χ))`
and `x ∈ x₀₀ (1 + ϖ^(a(χ) - j) M(O))`. -/
theorem fourierIntegral_twistedPrincipalFun_support (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : (T).additiveConductor ψ = 0)
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier) {j : ℕ} (hj : 0 < j)
    (hk : (T).multiplicativeConductor χ ≤ 2 * j) (hjk : j < (T).multiplicativeConductor χ)
    {x : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier}
    (hx : rectangularFourierIntegral ψ ν (twistedPrincipalFun F χ j) x ≠ 0) :
    (T).discreteValuation (x 0 0) = WithZero.exp ((T).multiplicativeConductor χ : ℤ) ∧
      (x 0 0)⁻¹ • x ∈ principalSet F n ((T).multiplicativeConductor χ - j) := by
  set k := (T).multiplicativeConductor χ with hkdef
  have hE := entry_character_eq F ψ ν χ hj hk hx
  -- off-diagonal entries lie in `ϖ^(-j) O`
  have hoff : ∀ r c, r ≠ c → x r c ∈ 𝓛 (j : ℤ) := by
    intro r c hrc
    have h := ((T).forall_mul_eq_one_iff_mem_additiveLattice ψ (-(j : ℤ)) (x r c)).1
      fun t ht => by
        have := hE r c t ht
        rw [ite_eq_right hrc] at this
        exact Circle.coe_eq_one.mp this
    rwa [hψ, zero_sub, neg_neg] at h
  -- diagonal entries agree with `x₀₀` modulo `ϖ^(-j) O`
  have hdiag : ∀ r, x r r - x 0 0 ∈ 𝓛 (j : ℤ) := by
    intro r
    have h := ((T).forall_mul_eq_one_iff_mem_additiveLattice ψ (-(j : ℤ)) (x r r - x 0 0)).1
      fun t ht => by
        have h1 := hE r r t ht
        have h0 := hE 0 0 t ht
        rw [ite_eq_left rfl] at h1 h0
        have h10 : ψ (t * x r r) = ψ (t * x 0 0) := Circle.coe_inj.mp (h1.trans h0.symm)
        rw [mul_sub, AddChar.map_sub_eq_div, h10, div_self']
    rwa [hψ, zero_sub, neg_neg] at h
  -- `x₀₀ ∈ ϖ^(-k) O`
  have hle : x 0 0 ∈ 𝓛 (k : ℤ) := by
    have h := ((T).forall_mul_eq_one_iff_mem_additiveLattice ψ (-(k : ℤ)) (x 0 0)).1
      fun t ht => by
        have htj : t ∈ 𝓛 (-(j : ℤ)) := (T).additiveLattice_mono (by omega) ht
        have h0 := hE 0 0 t htj
        rw [ite_eq_left rfl] at h0
        have hU : onePlusUnit F hj t htj ∈ (T).principalUnits k :=
          mem_principalUnits_of_sub_one_mem F (by omega : 0 < k) le_rfl _
            (by rw [onePlusUnit_val, add_sub_cancel_left]; exact ht)
        rw [(T).multiplicativeConductor_spec χ _ hU, Units.val_one] at h0
        exact Circle.coe_eq_one.mp h0
    rwa [hψ, zero_sub, neg_neg] at h
  -- `x₀₀ ∉ ϖ^(-(k-1)) O`, by minimality of the conductor
  have hnle : x 0 0 ∉ 𝓛 ((k : ℤ) - 1) := by
    intro hmem
    obtain ⟨w, hw, hχw⟩ := (T).exists_nontrivial_below_multiplicativeConductor χ (k - 1)
      (by omega)
    have hwt : (w : F.Carrier) - 1 ∈ 𝓛 (-((k - 1 : ℕ) : ℤ)) := hw.2
    have htj : (w : F.Carrier) - 1 ∈ 𝓛 (-(j : ℤ)) :=
      (T).additiveLattice_mono (by omega) hwt
    have h0 := hE 0 0 _ htj
    rw [ite_eq_left rfl] at h0
    have hwu : onePlusUnit F hj _ htj = w := Units.ext (by simp)
    rw [hwu] at h0
    have hψ1 := ((T).forall_mul_eq_one_iff_mem_additiveLattice ψ (-((k - 1 : ℕ) : ℤ)) (x 0 0)).2
      (by rw [hψ, zero_sub, neg_neg]; convert hmem using 2; omega) _ hwt
    apply hχw
    apply Units.ext
    rw [← h0, hψ1, Circle.coe_one, Units.val_one]
  have hv := valuation_eq_exp_of_le_of_not_le F hle hnle
  refine ⟨hv, ?_⟩
  -- the normalized matrix lies in `1 + ϖ^(k-j) M(O)`
  have hx0 : x 0 0 ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  have hinv : (x 0 0)⁻¹ ∈ 𝓛 (-(k : ℤ)) := by
    rw [PadicField.TopologicalData.mem_additiveLattice, map_inv₀, hv, ← WithZero.exp_neg]
  have hcast : -(((k - j : ℕ)) : ℤ) = -(k : ℤ) + j := by omega
  show (x 0 0)⁻¹ • x - 1 ∈ matrixLattice F n (-((k - j : ℕ) : ℤ))
  intro r c
  rw [hcast]
  by_cases hrc : r = c
  · subst hrc
    have h := mul_mem_lattice F hinv (hdiag r)
    convert h using 1
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq]
    field_simp
  · have h := mul_mem_lattice F hinv (hoff r c hrc)
    convert h using 1
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne hrc,
      sub_zero]

end Fourier

section Dual

variable {n : ℕ}

open Conductor UnequalRankMirabolicUnitTest

/-- `ω(g₀₀)⁻¹ χ(g₀₀)^(n+1) χ(det g)⁻¹`, and `0` when `g₀₀ = 0`. -/
def twistedEpsilonWeight (χ : Quasicharacter F.Carrier) (ω : F.Carrierˣ →* ℂˣ)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) : ℂ :=
  by classical exact if h : g.val 0 0 = 0 then 0 else
    (((ω (Units.mk0 (g.val 0 0) h))⁻¹ * χ (Units.mk0 (g.val 0 0) h) ^ (n + 1) *
      (χ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ)

theorem twistedEpsilonWeight_of_ne (χ : Quasicharacter F.Carrier) (ω : F.Carrierˣ →* ℂˣ)
    {g : Langlands.GeneralLinear (n + 1) F.Carrier} (h : g.val 0 0 ≠ 0) :
    twistedEpsilonWeight F χ ω g =
      (((ω (Units.mk0 (g.val 0 0) h))⁻¹ * χ (Units.mk0 (g.val 0 0) h) ^ (n + 1) *
        (χ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) := by
  unfold twistedEpsilonWeight
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- A matrix of the principal congruence set of positive level is an element of the
principal level subgroup of the same level. -/
theorem exists_mem_principalLevelSubgroup_of_mem_principalSet {a : ℕ} (ha : 0 < a)
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier} (hY : Y ∈ principalSet F n a) :
    ∃ E ∈ principalLevelSubgroup F.Carrier n a,
      (E : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) = Y :=
  exists_mem_principalLevelSubgroup ha Y fun i l => by
    rw [RankOneBox.levelSet_eq_additiveLattice F]
    exact hY i l

/-- The inverse transpose of an invertible matrix has the inverse determinant. -/
theorem det_inverseTranspose_eq (y : Langlands.GeneralLinear (n + 1) F.Carrier) :
    Matrix.GeneralLinearGroup.det (GeneralLinear.inverseTranspose (n + 1) F.Carrier y) =
      (Matrix.GeneralLinearGroup.det y)⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, GeneralLinear.inverseTranspose_coe,
    Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

/-- The inverse transpose of a scalar matrix is the inverse scalar matrix. -/
theorem inverseTranspose_scalar_eq (z : F.Carrierˣ) :
    GeneralLinear.inverseTranspose (n + 1) F.Carrier
        (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) z) =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) z⁻¹ := by
  apply Units.ext
  rw [GeneralLinear.inverseTranspose_coe, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar]
  simp

/-- The dual-side pointwise identity of Jacquet–Shalika §2.5. Let `ψ` have conductor
exponent `0`, let `a(χ) ≥ 2m'` with `m' ≥ 1`, and let `f` transform under the centre by
`ω` and under `K_{m'}` by `χ ∘ det`. Wherever the Fourier transform of the twisted
principal test does not vanish, `f((gᵀ)⁻¹) = f(1) ω(g₀₀)⁻¹ χ(g₀₀)^(n+1) χ(det g)⁻¹`, and
`det g` has order `-(n+1) a(χ)`. -/
theorem coefficientIota_eq_of_fourierIntegral_ne_zero (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : (T).additiveConductor ψ = 0) (ν : AdditiveHaarMeasure F.Carrier)
    (χ : Quasicharacter F.Carrier) (ω : F.Carrierˣ →* ℂˣ) {m' : ℕ} (hm' : 1 ≤ m')
    (hk : 2 * m' ≤ (T).multiplicativeConductor χ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf : ∀ (z : F.Carrierˣ), ∀ y ∈ Conductor.principalLevelSubgroup F.Carrier n m',
      f (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) z * y) =
        ((ω z : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * f 1)
    {g : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hg : rectangularFourierIntegral ψ ν
      (twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ))) g.val ≠ 0) :
    GodementJacquet.coefficientIota f g = f 1 * twistedEpsilonWeight F χ ω g ∧
      (T).ord (Matrix.det g.val) = -(((n + 1) * (T).multiplicativeConductor χ : ℕ) : ℤ) := by
  set k := (T).multiplicativeConductor χ with hkdef
  have hk1 : 1 ≤ k := by omega
  have hjeq : twistLevel k = (k + 1) / 2 := twistLevel_eq hk1
  have hj0 : 0 < twistLevel k := twistLevel_pos k
  have hjk : twistLevel k < k := by omega
  have hkj : k ≤ 2 * twistLevel k := le_two_mul_twistLevel k
  have hm'j : m' ≤ k - twistLevel k := by omega
  obtain ⟨hv, hmem⟩ := fourierIntegral_twistedPrincipalFun_support F ψ hψ ν χ hj0 hkj hjk hg
  have hx0 : g.val 0 0 ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  set z : F.Carrierˣ := Units.mk0 (g.val 0 0) hx0 with hz
  obtain ⟨y, hy, hyval⟩ :=
    exists_mem_principalLevelSubgroup_of_mem_principalSet F (by omega : 0 < k - twistLevel k) hmem
  -- `g = z · y` with `y ∈ K_{a(χ) - j}`
  have hgy : g = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) z * y := by
    apply Units.ext
    rw [Units.val_mul, hyval, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, smul_smul, hz, Units.val_mk0, mul_inv_cancel₀ hx0,
      one_smul]
  have hdet : Matrix.GeneralLinearGroup.det g = z ^ (n + 1) * Matrix.GeneralLinearGroup.det y := by
    rw [hgy, map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  refine ⟨?_, ?_⟩
  · have hιy : GeneralLinear.inverseTranspose (n + 1) F.Carrier y ∈
        principalLevelSubgroup F.Carrier n m' :=
      principalLevelSubgroup_antitone F.Carrier n hm'j
        (inverseTranspose_mem_principalLevelSubgroup F.Carrier n _ hy)
    have hιg : GeneralLinear.inverseTranspose (n + 1) F.Carrier g =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) z⁻¹ *
          GeneralLinear.inverseTranspose (n + 1) F.Carrier y := by
      rw [hgy, map_mul, inverseTranspose_scalar_eq]
    have hdetι : Matrix.GeneralLinearGroup.det
        (GeneralLinear.inverseTranspose (n + 1) F.Carrier y) =
          z ^ (n + 1) * (Matrix.GeneralLinearGroup.det g)⁻¹ := by
      rw [det_inverseTranspose_eq, hdet, mul_inv, mul_inv_cancel_left]
    unfold GodementJacquet.coefficientIota
    rw [hιg, hf _ _ hιy, twistedEpsilonWeight_of_ne F χ ω hx0, ← hz, hdetι, map_inv, map_mul,
      map_pow, map_inv]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    ring
  · -- `det g = g₀₀^(n+1) det y` with `det y` a valuation unit
    have hvy : (T).discreteValuation (Matrix.GeneralLinearGroup.det y : F.Carrier) = 1 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hyval]
      have h := valuation_det_one_add F (by omega : 0 < k - twistLevel k) hmem
      rwa [add_sub_cancel] at h
    have hdetv : Matrix.det g.val = g.val 0 0 ^ (n + 1) *
        (Matrix.GeneralLinearGroup.det y : F.Carrier) := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_mul, Units.val_pow_eq_pow_val,
        hz, Units.val_mk0]
    have hvd : (T).discreteValuation (Matrix.det g.val) =
        WithZero.exp ((((n + 1) * k : ℕ) : ℤ)) := by
      rw [hdetv, map_mul, hvy, mul_one, map_pow, hv, ← WithZero.exp_nsmul]
      congr 1
    rw [PadicField.TopologicalData.ord, hvd, WithZero.log_exp]

end Dual

end Langlands.RankinSelberg.UniformTwist
