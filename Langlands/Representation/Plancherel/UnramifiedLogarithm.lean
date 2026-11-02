import Langlands.Representation.Plancherel.UnramifiedCharacters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Normalized logarithms of norm characters

The additive index is intended to be the actual rational-character group.
The construction uses its given norm evaluations; it supplies no reductive
structure, finite-rank assertion, or rational-point topology.
-/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

universe uG uL

private theorem positiveUnit_pos (x : ℝ≥0ˣ) : 0 < ((x : ℝ≥0) : ℝ) := by
  exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero x))

/-- The coordinate with Waldspurger's sign convention `q ^ (-H) = norm`. -/
def normLog (q : ℝ) (x : ℝ≥0ˣ) : ℝ :=
  -Real.log ((x : ℝ≥0) : ℝ) / Real.log q

@[simp]
theorem normLog_one (q : ℝ) : normLog q 1 = 0 := by
  simp [normLog]

theorem normLog_mul (q : ℝ) (x y : ℝ≥0ˣ) :
    normLog q (x * y) = normLog q x + normLog q y := by
  simp only [normLog, Units.val_mul, NNReal.coe_mul]
  rw [Real.log_mul (positiveUnit_pos x).ne' (positiveUnit_pos y).ne', neg_add, add_div]

/-- The logarithm vanishes exactly at norm one, provided the base exceeds one. -/
theorem normLog_eq_zero_iff {q : ℝ} (hq : 1 < q) (x : ℝ≥0ˣ) :
    normLog q x = 0 ↔ x = 1 := by
  constructor
  · intro h
    have hlogq : Real.log q ≠ 0 := (Real.log_pos hq).ne'
    have hx := congrArg (fun r : ℝ => r * Real.log q) h
    simp only [normLog, div_mul_cancel₀ _ hlogq, zero_mul] at hx
    apply Units.ext
    apply NNReal.eq
    exact Real.eq_one_of_pos_of_log_eq_zero (positiveUnit_pos x) (neg_eq_zero.mp hx)
  · rintro rfl
    exact normLog_one q

/-- The normalized logarithm satisfies the defining exponential identity. -/
theorem rpow_neg_normLog {q : ℝ} (hq : 1 < q) (x : ℝ≥0ˣ) :
    q ^ (-normLog q x) = ((x : ℝ≥0) : ℝ) := by
  have hlogq : Real.log q ≠ 0 := (Real.log_pos hq).ne'
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hq)]
  have hexp : Real.log q * (-normLog q x) = Real.log ((x : ℝ≥0) : ℝ) := by
    simp only [normLog, neg_div, neg_neg]
    exact mul_div_cancel₀ _ hlogq
  rw [hexp, Real.exp_log (positiveUnit_pos x)]

/-- The exponential identity uniquely determines the normalized logarithm. -/
theorem normLog_eq_of_rpow {q : ℝ} (hq : 1 < q) (x : ℝ≥0ˣ) (t : ℝ)
    (h : q ^ (-t) = ((x : ℝ≥0) : ℝ)) : normLog q x = t := by
  have hlogq : Real.log q ≠ 0 := (Real.log_pos hq).ne'
  rw [normLog, ← h, Real.log_rpow (lt_trans zero_lt_one hq), neg_mul, neg_neg,
    mul_div_cancel_right₀ _ hlogq]

variable {G : Type uG} [Group G] {L : Type uL} [AddCommGroup L]

/-- For fixed `g`, norm evaluation followed by the normalized logarithm is
additive in the character. No basis of `L` is chosen. -/
def normLogPairing (q : ℝ) (ν : L →+ Additive (G →* ℝ≥0ˣ)) (g : G) : L →+ ℝ where
  toFun χ := normLog q ((ν χ).toMul g)
  map_zero' := by
    rw [map_zero]
    exact normLog_one q
  map_add' χ ψ := by
    rw [map_add]
    exact normLog_mul q _ _

/-- The logarithm as a homomorphism into the real additive dual of the
character group, written multiplicatively only to match the source group. -/
def normLogarithm (q : ℝ) (ν : L →+ Additive (G →* ℝ≥0ˣ)) :
    G →* Multiplicative (L →+ ℝ) where
  toFun g := Multiplicative.ofAdd (normLogPairing q ν g)
  map_one' := by
    apply AddMonoidHom.ext
    intro χ
    change normLog q ((ν χ).toMul 1) = 0
    rw [map_one, normLog_one]
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro χ
    change normLog q ((ν χ).toMul (g * h)) =
      normLog q ((ν χ).toMul g) + normLog q ((ν χ).toMul h)
    rw [map_mul, normLog_mul]

@[simp]
theorem normLogarithm_apply (q : ℝ) (ν : L →+ Additive (G →* ℝ≥0ˣ)) (g : G) (χ : L) :
    (normLogarithm q ν g).toAdd χ =
      -Real.log (((ν χ).toMul g : ℝ≥0) : ℝ) / Real.log q := rfl

/-- Waldspurger's defining relation, evaluated on any character. -/
theorem normLogarithm_spec {q : ℝ} (hq : 1 < q)
    (ν : L →+ Additive (G →* ℝ≥0ˣ)) (g : G) (χ : L) :
    q ^ (-(normLogarithm q ν g).toAdd χ) = (((ν χ).toMul g : ℝ≥0) : ℝ) :=
  rpow_neg_normLog hq _

/-- The logarithm uses the same norm-one subgroup as the published
unramified-character construction. -/
theorem normLogarithm_ker {q : ℝ} (hq : 1 < q)
    (ν : L →+ Additive (G →* ℝ≥0ˣ)) :
    (normLogarithm q ν).ker = commonNormKernel (fun χ => (ν χ).toMul) := by
  ext g
  rw [mem_commonNormKernel]
  change normLogPairing q ν g = 0 ↔ ∀ χ, (ν χ).toMul g = 1
  constructor
  · intro h χ
    apply (normLog_eq_zero_iff hq _).mp
    exact DFunLike.congr_fun h χ
  · intro h
    apply AddMonoidHom.ext
    intro χ
    exact (normLog_eq_zero_iff hq _).mpr (h χ)

/-- Comparison with integer-valued character evaluations. The normalization
premise is a pointwise identity for the given maps, not a lattice assertion. -/
theorem normLogarithm_eq_intValuation {q : ℝ} (hq : 1 < q)
    (ν : L →+ Additive (G →* ℝ≥0ˣ)) (v : G →* Multiplicative (L →+ ℤ))
    (h : ∀ g χ, q ^ (-((v g).toAdd χ : ℝ)) = (((ν χ).toMul g : ℝ≥0) : ℝ))
    (g : G) (χ : L) :
    (normLogarithm q ν g).toAdd χ = ((v g).toAdd χ : ℝ) :=
  normLog_eq_of_rpow hq _ _ (h g χ)

end Langlands.Plancherel
