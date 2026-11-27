import Langlands.Global.RelativeRootChamberLog

/-! # Removing the integral part of a fundamental Siegel ray -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.PositiveRealTorus

open GroupScheme AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T₀ T : CommGroupScheme (Spec (CommRingCat.of F))}
  (j : T₀ ⟶ T) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "Torus" => intrinsicSubgroup F T₀
local notation "Δ" => simpleRelativeRoots i ν
local notation "rootLog" => (fun (a : Torus) (β : characterLattice T) =>
  characterLog F T₀.toGrp (Subtype.val a) (j ≫ β))
local notation "chamber" => weakSimpleRootChamber F T₀ T j G i ν
local notation "logT" => (fun (t : ℝ≥0ˣ) => Real.log ((t : ℝ≥0) : ℝ))

/-- After removing an integral power of a fundamental ray, the remaining point lies in
the same chamber. Its log at the distinguished root is within one ray step of the lower
threshold, and every other simple-root log is unchanged. -/
theorem exists_siegelChamber_rayFactor
    (t : ℝ≥0ˣ) {α : characterLattice T} (hα : α ∈ Δ)
    (r : Torus) (hPos : 0 < rootLog r α)
    (hOff : ∀ β ∈ Δ, β ≠ α → rootLog r β = 0)
    (a : Torus) (ha : a ∈ chamber t) :
    ∃ (n : ℕ) (b : Torus), a = r ^ n * b ∧ b ∈ chamber t ∧
      (∀ β ∈ Δ, rootLog b β ≤ rootLog a β) ∧
      (∀ β ∈ Δ, β ≠ α → rootLog b β = rootLog a β) ∧
      rootLog b α < logT t + rootLog r α ∧
      ∀ q : ℝ, 0 < q → q < 1 →
        let ε := -Real.log q / rootLog r α
        q ^ n ≤ Real.exp (ε * (logT t + rootLog r α)) * Real.exp (-ε * rootLog a α) := by
  classical
  have hLow := (mem_weakSimpleRootChamber_iff_log F T₀ T j G i ν t a).mp ha
  let u := (rootLog a α - logT t) / rootLog r α
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr (hLow α hα)) hPos.le
  let n := ⌊u⌋₊
  let b := (r ^ n)⁻¹ * a
  have hEq : a = r ^ n * b := (mul_inv_cancel_left (r ^ n) a).symm
  have hPow (n : ℕ) (β : characterLattice T) : rootLog (r ^ n) β = (n : ℝ) * rootLog r β := by
    induction n with
    | zero =>
      simp only [pow_zero, OneMemClass.coe_one, characterLog_one, Nat.cast_zero, zero_mul]
      rfl
    | succ n ih =>
      change characterLog F T₀.toGrp (r ^ (n + 1)).val (j ≫ β) =
        ((n + 1 : ℕ) : ℝ) * rootLog r β
      rw [pow_succ, Subgroup.coe_mul, characterLog_mul]
      change rootLog (r ^ n) β + rootLog r β = _
      rw [ih, Nat.cast_succ, add_mul, one_mul]
  have hB (β : characterLattice T) : rootLog b β = rootLog a β - (n : ℝ) * rootLog r β := by
    have h := congrArg (fun x : Torus => rootLog x β) hEq
    simp only [Subgroup.coe_mul, characterLog_mul] at h
    change rootLog a β = rootLog (r ^ n) β + rootLog b β at h
    rw [hPow] at h
    linarith
  have hFloor : (n : ℝ) * rootLog r α ≤ rootLog a α - logT t :=
    (le_div_iff₀ hPos).mp (Nat.floor_le hu)
  have hCeil : rootLog a α - logT t < ((n : ℝ) + 1) * rootLog r α :=
    (div_lt_iff₀ hPos).mp (Nat.lt_floor_add_one u)
  have hOther (β : characterLattice T) (hβ : β ∈ Δ) (hne : β ≠ α) :
      rootLog b β = rootLog a β := by
    rw [hB, hOff β hβ hne, mul_zero, sub_zero]
  refine ⟨n, b, hEq, (mem_weakSimpleRootChamber_iff_log F T₀ T j G i ν t b).mpr ?_, ?_,
    hOther, ?_, ?_⟩
  · intro β hβ
    change logT t ≤ rootLog b β
    by_cases he : β = α
    · subst β
      rw [hB]
      linarith
    · rw [hOther β hβ he]
      exact hLow β hβ
  · intro β hβ
    by_cases he : β = α
    · subst β
      rw [hB]
      exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hPos.le)
    · exact (hOther β hβ he).le
  · rw [hB]
    linarith
  · intro q hq hq₁
    let ε := -Real.log q / rootLog r α
    change q ^ n ≤ Real.exp (ε * (logT t + rootLog r α)) * Real.exp (-ε * rootLog a α)
    have hε : 0 ≤ ε := div_nonneg (neg_nonneg.mpr (Real.log_neg hq hq₁).le) hPos.le
    have hLog : ε * rootLog r α = -Real.log q := div_mul_cancel₀ _ hPos.ne'
    have hCeil' : rootLog a α - (logT t + rootLog r α) ≤ (n : ℝ) * rootLog r α := by
      linarith
    calc
      q ^ n = Real.exp ((n : ℝ) * Real.log q) := by rw [Real.exp_nat_mul, Real.exp_log hq]
      _ ≤ Real.exp (ε * (logT t + rootLog r α) + -ε * rootLog a α) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hCeil' hε
        rw [mul_left_comm ε, hLog] at h
        linarith
      _ = _ := Real.exp_add _ _

end Langlands.Global.PositiveRealTorus

namespace Langlands.Global

open GroupScheme AdelicGroupPoints PositiveRealTorus

/-- An integral power of a fundamental ray accounts for the large part of a single
simple-root logarithm without changing the other simple-root logarithms. -/
def AdelicSiegelRayCoordinatesStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (T₀ T : CommGroupScheme (Spec (CommRingCat.of F)))
    (j : T₀ ⟶ T) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    let Δ := simpleRelativeRoots i ν
    let L := fun (a : intrinsicSubgroup F T₀) (β : characterLattice T) =>
      characterLog F T₀.toGrp a.val (j ≫ β)
    ∀ (t : ℝ≥0ˣ) (α : Δ) (r : intrinsicSubgroup F T₀),
      0 < L r α.val → (∀ β ∈ Δ, β ≠ α.val → L r β = 0) →
      ∀ a : intrinsicSubgroup F T₀, a ∈ weakSimpleRootChamber F T₀ T j G i ν t →
        ∃ (n : ℕ) (b : intrinsicSubgroup F T₀),
          a = r ^ n * b ∧ b ∈ weakSimpleRootChamber F T₀ T j G i ν t ∧
          (∀ β ∈ Δ, L b β ≤ L a β) ∧ (∀ β ∈ Δ, β ≠ α.val → L b β = L a β) ∧
          L b α.val < Real.log ((t : ℝ≥0) : ℝ) + L r α.val ∧
          ∀ q : ℝ, 0 < q → q < 1 →
            let ε := -Real.log q / L r α.val
            q ^ n ≤ Real.exp (ε * (Real.log ((t : ℝ≥0) : ℝ) + L r α.val)) *
              Real.exp (-ε * L a α.val)

theorem adelicSiegelRayCoordinates : AdelicSiegelRayCoordinatesStatement := by
  intro F _ _ G _ T₀ T j i ν
  dsimp only
  intro t α r hPos hOff a ha
  exact exists_siegelChamber_rayFactor j i ν t α.property r hPos hOff a ha

end Langlands.Global
