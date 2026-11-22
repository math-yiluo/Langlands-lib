import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.Global.SimpleRootBoxCompact

/-! # Heights of positive torus points in spanning character coordinates -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan AdelicGroupPoints PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) {N : ℕ} (rho : MatrixRepresentation G (Fin N))
  (S : Set (characterLattice T))

/-- The representation height of an intrinsic positive torus point is bounded exponentially
in a common absolute bound for the logarithms of a rationally spanning set of character norms. -/
def AdelicPositiveTorusLogHeightBoundStatement : Prop :=
  IsSplitTorus T.toGrp → ratSpan S = ⊤ → 0 < N →
  ∃ C r : ℝ, 1 ≤ C ∧ 0 ≤ r ∧ ∀ a : intrinsicSubgroup F T, ∀ B : ℝ, 0 ≤ B →
    (∀ χ ∈ S, |logNormHom F T a.val χ| ≤ B) →
    adelicHeight F G rho (map F T.toGrp G i a) ≤ C * Real.exp (r * B)

theorem adelicPositiveTorusLogHeightBound : AdelicPositiveTorusLogHeightBoundStatement i rho S := by
  intro hT hS hN
  classical
  obtain ⟨I, _, ⟨e₀⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let J := ULift.{u} (Fin n)
  let σ : J ≃ I := Equiv.ulift.trans (Fintype.equivFin I).symm
  let e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J :=
    e₀ ≪≫ LocalSplitCell.exponentEquivGroupIso _ (LinearEquiv.funCongrLeft ℤ ℤ σ)
  obtain ⟨C, hC, m, hH⟩ := exists_adelicHeight_map_full_le F rho hN T i e
  have hcoef (k : J) := exists_abs_le_of_toRat_mem_ratSpan
    (c := coordinateCharacter F J T e k) (hS ▸ Submodule.mem_top)
  choose K hK hlog using hcoef
  let d := (Module.finrank ℚ F : ℝ)
  have hd : 0 < d := Nat.cast_pos.mpr Module.finrank_pos
  let r := ∑ k, K k / d
  have hr : 0 ≤ r := Finset.sum_nonneg fun k _ => div_nonneg (hK k) hd.le
  refine ⟨max 1 C, (m : ℝ) * r, le_max_left _ _, mul_nonneg (Nat.cast_nonneg _) hr, ?_⟩
  intro a B _ hB
  obtain ⟨x, rfl⟩ := fullIntrinsic_surjective F T J e a
  let ℓ := logNormHom F T (full F J T e x)
  have hmax (k : J) :
      ((max (x k : ℝ≥0) (((x k)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp (K k / d * B) := by
    have hχ : positiveCharacter F J T e (coordinateCharacter F J T e k) x = x k := by
      have h := characterValue_full F J T e (coordinateCharacter F J T e k) x
      rw [characterValue_coordinateCharacter, coordinates_full] at h
      exact (PositiveRealIdeles.full_injective F h).symm
    have he : ℓ (coordinateCharacter F J T e k) =
        d * Real.log ((x k : ℝ≥0) : ℝ) := by
      change Real.log ((normCharacter F T (coordinateCharacter F J T e k)
        (full F J T e x) : ℝ≥0) : ℝ) = _
      rw [normCharacter_apply, absoluteValue_characterValue_full, hχ, Units.val_pow_eq_pow_val,
        NNReal.coe_pow, Real.log_pow]
    have hh := hlog k ℓ B hB
    rw [he, abs_mul, abs_of_pos hd] at hh
    have habs : |Real.log ((x k : ℝ≥0) : ℝ)| ≤ K k / d * B := by
      calc
        _ ≤ K k * B / d := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hh)
        _ = _ := by ring
    have hx : 0 < ((x k : ℝ≥0) : ℝ) := by exact_mod_cast (x k).ne_zero.bot_lt
    rw [NNReal.coe_max, Units.val_inv_eq_inv_val, NNReal.coe_inv]
    apply max_le
    · rw [← Real.exp_log hx]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans habs)
    · rw [← Real.exp_log (inv_pos.mpr hx), Real.log_inv]
      exact Real.exp_le_exp.mpr ((neg_le_abs _).trans habs)
  have hsize : ((positiveSize x : ℝ≥0) : ℝ) ≤ Real.exp (r * B) := by
    simp only [positiveSize, NNReal.coe_prod, r, Finset.sum_mul, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) (fun k _ => hmax k)
  calc
    adelicHeight F G rho (map F T.toGrp G i (fullIntrinsic F T J e x)) ≤
        C * ((positiveSize x : ℝ≥0) : ℝ) ^ m := hH x
    _ ≤ max 1 C * (Real.exp (r * B)) ^ m := by
      exact mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) hsize _)
        (pow_nonneg (NNReal.coe_nonneg _) _) (le_trans zero_le_one (le_max_left _ _))
    _ = max 1 C * Real.exp ((m : ℝ) * r * B) := by
      rw [← Real.exp_nat_mul, mul_assoc]

end Langlands.Global.RepresentationGrowth
