import Langlands.Global.FunctionFieldValuationPlaces
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # Real absolute-value places of function fields -/

noncomputable section

universe u

open AlgebraicCurve
open scoped NNReal

namespace Langlands.Global

section AbsoluteValueValuation

variable {F : Type u} [Field F]

/-- The NNReal-valued valuation associated to a nonarchimedean absolute value. -/
def absoluteValueValuation (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) :
    Valuation F ℝ≥0 where
  toFun x := ⟨a x, a.nonneg x⟩
  map_zero' := by
    apply NNReal.eq
    change a 0 = 0
    exact map_zero a
  map_one' := by
    apply NNReal.eq
    change a 1 = 1
    exact map_one a
  map_mul' x y := by
    apply NNReal.eq
    change a (x * y) = a x * a y
    exact map_mul a x y
  map_add_le_max' x y := ha x y

@[simp]
theorem coe_absoluteValueValuation (a : AbsoluteValue F ℝ)
    (ha : IsNonarchimedean a) (x : F) :
    ((absoluteValueValuation a ha x : ℝ≥0) : ℝ) = a x := rfl

/-- A nontrivial absolute value gives a proper valuation subring. -/
theorem absoluteValueValuation_ne_top (a : AbsoluteValue F ℝ)
    (ha : IsNonarchimedean a) (hne : a.IsNontrivial) :
    (absoluteValueValuation a ha).valuationSubring ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hne.exists_abv_gt_one
  intro h
  have hm : x ∈ (absoluteValueValuation a ha).valuationSubring := by rw [h]; trivial
  exact (not_le_of_gt hx) hm

/-- A rank-one valuation gives a real absolute value using its rank-one embedding. -/
def rankOneValuationAbsoluteValue {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) [v.RankOne] : AbsoluteValue F ℝ where
  toFun := v.norm
  map_mul' x y := by simp [Valuation.norm, ← NNReal.coe_mul, map_mul]
  nonneg' := v.norm_nonneg
  eq_zero' x := ⟨v.norm_eq_zero, fun h => by simp [h, Valuation.norm]⟩
  add_le' x y := (v.norm_add_le x y).trans
    (max_le_add_of_nonneg (v.norm_nonneg x) (v.norm_nonneg y))

theorem rankOneValuationAbsoluteValue_le_iff
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) [v.RankOne] (x y : F) :
    rankOneValuationAbsoluteValue v x ≤ rankOneValuationAbsoluteValue v y ↔ v x ≤ v y := by
  change (v.norm x ≤ v.norm y) ↔ _
  simp only [Valuation.norm, NNReal.coe_le_coe,
    (Valuation.RankOne.strictMono v).le_iff_le, Valuation.restrict_le_iff]

theorem rankOneValuationAbsoluteValue_nonarchimedean
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) [v.RankOne] :
    IsNonarchimedean (rankOneValuationAbsoluteValue v) := v.norm_add_le

theorem rankOneValuationAbsoluteValue_nontrivial
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) [v.RankOne] :
    (rankOneValuationAbsoluteValue v).IsNontrivial := by
  obtain ⟨x, hx0, hx1⟩ := Valuation.RankOne.nontrivial v
  refine ⟨x, v.ne_zero_iff.mp hx0, ?_⟩
  intro hx
  have h := (rankOneValuationAbsoluteValue_le_iff v x 1)
  have h' := (rankOneValuationAbsoluteValue_le_iff v 1 x)
  simp only [map_one] at h h'
  exact hx1 (le_antisymm (h.mp hx.le) (h'.mp hx.ge))

/-- Converting a rank-one valuation through real absolute values retains its
comparison preorder. -/
theorem rankOneValuationAbsoluteValue_valuation_isEquiv
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) [v.RankOne] :
    (absoluteValueValuation (rankOneValuationAbsoluteValue v)
      (rankOneValuationAbsoluteValue_nonarchimedean v)).IsEquiv v := by
  intro x y
  exact rankOneValuationAbsoluteValue_le_iff v x y

/-- All nontrivial real absolute values, before passing to equivalence classes. -/
abbrev NontrivialRealAbsoluteValue := {a : AbsoluteValue F ℝ // a.IsNontrivial}

/-- The usual equivalence relation, restricted to nontrivial absolute values. -/
def nontrivialRealAbsoluteValueSetoid : Setoid (NontrivialRealAbsoluteValue (F := F)) :=
  Setoid.comap Subtype.val inferInstance

/-- Places presented by equivalence classes of all nontrivial real absolute values. -/
abbrev RealAbsoluteValuePlace :=
  Quotient (nontrivialRealAbsoluteValueSetoid (F := F))

end AbsoluteValueValuation

section FiniteConstants

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]

/-- A real absolute value is bounded by one on finite constants. -/
theorem finiteConstants_absoluteValue_le_one (a : AbsoluteValue F ℝ) (x : k) :
    a (algebraMap k F x) ≤ 1 := by
  classical
  let := Fintype.ofFinite k
  by_cases hx : x = 0
  · simp [hx]
  have hp : a (algebraMap k F x) ^ (Fintype.card k - 1) = 1 := by
    rw [← map_pow, ← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one, map_one]
  have hn : Fintype.card k - 1 ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt Fintype.one_lt_card)
  exact le_of_eq ((pow_eq_one_iff_of_nonneg (a.nonneg _) hn).mp hp)

include k in
/-- Every real absolute value is nonarchimedean in the presence of finite constants. -/
theorem finiteConstants_absoluteValue_isNonarchimedean (a : AbsoluteValue F ℝ) :
    IsNonarchimedean a := by
  have hn (n : ℕ) : ‖(n : WithAbs a)‖ ≤ 1 := by
    change a (n : F) ≤ 1
    simpa using finiteConstants_absoluteValue_le_one k F a (n : k)
  let : IsUltrametricDist (WithAbs a) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hn
  intro x y
  exact IsUltrametricDist.norm_add_le_max (WithAbs.toAbs a x) (WithAbs.toAbs a y)

end FiniteConstants

/-- Choose base two for the real realization of a curve place's discrete valuation. -/
instance curvePlaceAdicValuationRankOne
    {k F : Type u} [Field k] [Field F] [Algebra k F] (p : Place k F) :
    p.adicValuation.RankOne :=
  Valuation.IsRankOneDiscrete.rankOne p.adicValuation (show (1 : ℝ≥0) < 2 by norm_num)

section FunctionField

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- The actual curve place of a nontrivial real absolute value. -/
def functionFieldPlaceOfAbsoluteValue (a : NontrivialRealAbsoluteValue (F := F)) :
    Place k F :=
  (curvePlaceValuationRingEquiv k F).symm
    ⟨(absoluteValueValuation a.val
      (finiteConstants_absoluteValue_isNonarchimedean k F a.val)).valuationSubring,
      absoluteValueValuation_ne_top _ _ a.property⟩

@[simp]
theorem functionFieldPlaceOfAbsoluteValue_mem
    (a : NontrivialRealAbsoluteValue (F := F)) (x : F) :
    x ∈ (functionFieldPlaceOfAbsoluteValue k F a).toValuationSubring ↔ a.val x ≤ 1 :=
  Iff.rfl

/-- The valuation of an absolute value and the place's discrete valuation are
equivalent as valuations of the original field. -/
theorem functionFieldAbsoluteValueValuation_isEquiv_adicValuation
    (a : NontrivialRealAbsoluteValue (F := F)) :
    (absoluteValueValuation a.val
      (finiteConstants_absoluteValue_isNonarchimedean k F a.val)).IsEquiv
        (functionFieldPlaceOfAbsoluteValue k F a).adicValuation :=
  (functionFieldPlaceOfAbsoluteValue k F a).isEquiv_adicValuation_of_valuationSubring_eq rfl

theorem functionFieldPlaceOfAbsoluteValue_eq_iff
    (a b : NontrivialRealAbsoluteValue (F := F)) :
    functionFieldPlaceOfAbsoluteValue k F a = functionFieldPlaceOfAbsoluteValue k F b ↔
      a.val.IsEquiv b.val := by
  constructor
  · intro h
    have hv := (Valuation.isEquiv_iff_valuationSubring
      (absoluteValueValuation a.val (finiteConstants_absoluteValue_isNonarchimedean k F a.val))
      (absoluteValueValuation b.val (finiteConstants_absoluteValue_isNonarchimedean k F b.val))).mpr
        (congrArg Place.toValuationSubring h)
    exact hv
  · intro h
    apply Place.ext
    exact (Valuation.isEquiv_iff_valuationSubring _ _).mp h

/-- A chosen nontrivial real absolute value representing a curve place. -/
def curvePlaceRealAbsoluteValue (p : Place k F) : NontrivialRealAbsoluteValue (F := F) :=
  ⟨rankOneValuationAbsoluteValue p.adicValuation,
    rankOneValuationAbsoluteValue_nontrivial p.adicValuation⟩

@[simp]
theorem functionFieldPlaceOfAbsoluteValue_curvePlaceRealAbsoluteValue (p : Place k F) :
    functionFieldPlaceOfAbsoluteValue k F (curvePlaceRealAbsoluteValue k F p) = p := by
  apply Place.ext
  exact ((Valuation.isEquiv_iff_valuationSubring _ _).mp
    (rankOneValuationAbsoluteValue_valuation_isEquiv p.adicValuation)).trans
      p.adicValuation_valuationSubring

/-- The actual quotient of all nontrivial real absolute values agrees with the
concrete curve-place model over finite constants. -/
def realAbsoluteValuePlaceCurvePlaceEquiv :
    RealAbsoluteValuePlace (F := F) ≃ Place k F where
  toFun := Quotient.lift (functionFieldPlaceOfAbsoluteValue k F) fun a b h =>
    (functionFieldPlaceOfAbsoluteValue_eq_iff k F a b).mpr h
  invFun p := Quotient.mk _ (curvePlaceRealAbsoluteValue k F p)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      apply Quotient.sound
      apply (functionFieldPlaceOfAbsoluteValue_eq_iff k F _ a).mp
      exact functionFieldPlaceOfAbsoluteValue_curvePlaceRealAbsoluteValue k F _
  right_inv := functionFieldPlaceOfAbsoluteValue_curvePlaceRealAbsoluteValue k F

@[simp]
theorem realAbsoluteValuePlaceCurvePlaceEquiv_apply_mk
    (a : NontrivialRealAbsoluteValue (F := F)) :
    realAbsoluteValuePlaceCurvePlaceEquiv k F (Quotient.mk _ a) =
      functionFieldPlaceOfAbsoluteValue k F a := rfl

@[simp]
theorem realAbsoluteValuePlaceCurvePlaceEquiv_symm_apply (p : Place k F) :
    (realAbsoluteValuePlaceCurvePlaceEquiv k F).symm p =
      Quotient.mk _ (curvePlaceRealAbsoluteValue k F p) := rfl

end FunctionField

end Langlands.Global
