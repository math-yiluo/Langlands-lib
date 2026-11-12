import Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement
import Mathlib.Tactic

/-!
# The curve-family estimate from a bounded plane comparison

The geometric comparison is an explicit prerequisite. The arithmetic reduction
uses only Schmidt's bound and the uniform upper bound already present in the
published target.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

private theorem pureDimension_eq_dimension_of_irreducible
    (X : Scheme.{u}) [IrreducibleSpace X] (d : ℕ)
    (h : SchemeFiberGeometry.HasPureDimension X d) :
    topologicalKrullDim X = (d : WithBot ℕ∞) := by
  have hdim := h Set.univ (by simp [irreducibleComponents_eq_singleton])
  exact ((Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq _).symm.trans hdim

/-- A bounded geometric plane comparison and the two original point-count
hypotheses give the uniform curve-family estimate. -/
theorem familyLangWeilCurve_of_planeComparison
    (hcompare : FamilyCurvePlaneComparisonStatement.{u}) :
    FamilyLangWeilCurveStatement.{u} := by
  intro hplane hupper S X f hS hcompact hft hqc hgeom hdim
  let := hgeom
  obtain ⟨A, hA, hupperA⟩ := hupper S X f hS hcompact hft hqc
  obtain ⟨B, hB, hcompareB⟩ :=
    hcompare hupper S X f hS hcompact hft hqc hgeom hdim
  let T : ℕ := B + 9 * (B + 1) ^ 2 * (B + 1) ^ 2
  let D : ℝ := (B : ℝ) + 2 * (B : ℝ) ^ 3
  let C : ℝ := (A + 1) * (T + 1) + D + 1
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hD0 : 0 ≤ D := by positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro κ _ _ s
  let q : ℝ := Nat.card κ
  let N : ℝ := Nat.card {x : Spec (CommRingCat.of κ) ⟶ X // x ≫ f = s}
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.card_pos (α := κ)))
  have hq0 : 0 ≤ q := le_trans zero_le_one hq1
  have hsqrt1 : 1 ≤ Real.sqrt q := by
    exact (Real.le_sqrt (by norm_num) hq0).mpr (by simpa using hq1)
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hpow : q ^ ((1 : ℝ) - 1 / 2) = Real.sqrt q := by
    norm_num [Real.sqrt_eq_rpow]
  simp only [Nat.cast_one, pow_one]
  change |N - q| ≤ C * q ^ ((1 : ℝ) - 1 / 2)
  rw [hpow]
  by_cases hlarge : T < Nat.card κ
  · have hBq : B < Nat.card κ := lt_of_le_of_lt (Nat.le_add_right _ _) hlarge
    obtain ⟨p, hp, hp0, hp0B, hp1, hp1B, herror⟩ := hcompareB κ s hBq
    have hthreshold :
        9 * (p.degreeOf 0 + 1) ^ 2 * (p.degreeOf 1 + 1) ^ 2 < Nat.card κ := by
      calc
        _ ≤ 9 * (B + 1) ^ 2 * (B + 1) ^ 2 := by
          gcongr
        _ ≤ T := Nat.le_add_left _ _
        _ < Nat.card κ := hlarge
    have hplaneP := hplane κ p hp hp0 hp1 hthreshold
    let M : ℝ := Nat.card {v : Fin 2 → κ // MvPolynomial.eval v p = 0}
    have hcoeff :
        (min (p.degreeOf 0 ^ 2 * p.degreeOf 1)
          (p.degreeOf 1 ^ 2 * p.degreeOf 0) : ℕ) ≤ B ^ 3 := by
      calc
        _ ≤ p.degreeOf 0 ^ 2 * p.degreeOf 1 := min_le_left _ _
        _ ≤ B ^ 2 * B := by gcongr
        _ = B ^ 3 := by ring
    have hcoeffR :
        (min (p.degreeOf 0 ^ 2 * p.degreeOf 1)
          (p.degreeOf 1 ^ 2 * p.degreeOf 0) : ℕ) ≤ (B : ℝ) ^ 3 := by
      exact_mod_cast hcoeff
    have hplaneM : |M - q| ≤ 2 * (B : ℝ) ^ 3 * Real.sqrt q := by
      apply le_trans (le_of_lt hplaneP)
      gcongr
    have hmain : |N - q| ≤ D * Real.sqrt q := by
      calc
        |N - q| ≤ |N - M| + |M - q| := abs_sub_le _ _ _
        _ ≤ (B : ℝ) + 2 * (B : ℝ) ^ 3 * Real.sqrt q :=
          add_le_add herror hplaneM
        _ ≤ (B : ℝ) * Real.sqrt q + 2 * (B : ℝ) ^ 3 * Real.sqrt q := by
          exact add_le_add (le_mul_of_one_le_right hB0 hsqrt1) le_rfl
        _ = D * Real.sqrt q := by dsimp [D]; ring
    have hDC : D ≤ C := by
      dsimp [C]
      linarith [show 0 ≤ (A + 1) * ((T : ℝ) + 1) by positivity]
    exact hmain.trans (mul_le_mul_of_nonneg_right hDC hsqrt0)
  · have hqT : q ≤ T := by
      dsimp [q]
      exact_mod_cast (le_of_not_gt hlarge)
    have hfiberdim :
        topologicalKrullDim (f.fiber (s (IsLocalRing.closedPoint κ))) ≤
          (1 : WithBot ℕ∞) :=
      (pureDimension_eq_dimension_of_irreducible _ 1 (hdim _)).le
    have hN : N ≤ A * q := by
      simpa only [pow_one] using hupperA κ s 1 hfiberdim
    have hN0 : 0 ≤ N := Nat.cast_nonneg _
    have hsmall : |N - q| ≤ (A + 1) * (T + 1) * Real.sqrt q := by
      calc
        |N - q| ≤ N + q := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
        _ ≤ (A + 1) * q := by nlinarith
        _ ≤ (A + 1) * (T + 1) := by gcongr; linarith
        _ ≤ (A + 1) * (T + 1) * Real.sqrt q := by
          exact le_mul_of_one_le_right (by positivity) hsqrt1
    exact hsmall.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hsqrt0)

end Langlands.AlgebraicGeometry.LangWeil
