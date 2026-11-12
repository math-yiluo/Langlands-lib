import Langlands.Global.AdelicNormOneCompactCover
import Langlands.Global.SimpleRootBoxCompact
import Langlands.Global.PositiveRealTorusLog
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Compact rational representatives for split-torus character boxes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme PositiveRealTorus Langlands.LinearAlgebra.RationalSpan

variable (F : Type u) [Field F] [NumberField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Actual torus points whose normalized character norms lie in a symmetric box. -/
def torusCharacterBox (S : Set (characterLattice T)) (b : ℝ≥0) :
    Set (AdelicGroupPoints F T.toGrp) :=
  {x | ∀ χ ∈ S, b⁻¹ ≤ (normCharacter F T χ x : ℝ≥0) ∧
    (normCharacter F T χ x : ℝ≥0) ≤ b}

/-- Two-sided normalized norm bounds transfer to any finite character family in the
rational span of the bounded characters. The actual group need not be split. -/
theorem exists_characterBox_bound_of_ratSpan_le
    {S R : Set (characterLattice T)} (hR : R.Finite)
    (hspan : ratSpan R ≤ ratSpan S) (b : ℝ≥0) :
    ∃ d : ℝ≥0ˣ, torusCharacterBox F T S b ⊆ torusCharacterBox F T R (d : ℝ≥0) := by
  classical
  let : Fintype R := hR.fintype
  have hcoef : ∀ χ : R, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : characterLattice T →+ ℝ) (B : ℝ),
        (∀ ψ ∈ S, |ℓ ψ| ≤ B) → |ℓ χ.val| ≤ C * B := by
    intro χ
    apply exists_abs_le_of_toRat_mem_ratSpan
    exact hspan (Submodule.subset_span ⟨χ.val, χ.property, rfl⟩)
  choose C hC0 hC using hcoef
  let D : ℝ := (∑ χ : R, C χ) * |Real.log (b : ℝ)|
  refine ⟨expUnit D, fun x hx χ hχ => ?_⟩
  have hB : ∀ ψ ∈ S, |logNormHom F T x ψ| ≤ |Real.log (b : ℝ)| :=
    fun ψ hψ => abs_log_le_of_mem_Icc (Units.ne_zero _) (hx ψ hψ).1 (hx ψ hψ).2
  have hlog : |logNormHom F T x χ| ≤ D := by
    apply (hC ⟨χ, hχ⟩ (logNormHom F T x) _ hB).trans
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun ψ _ => hC0 ψ) (Finset.mem_univ (⟨χ, hχ⟩ : R)))
      (abs_nonneg _)
  have hpos : 0 < ((normCharacter F T χ x : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  change |Real.log ((normCharacter F T χ x : ℝ≥0) : ℝ)| ≤ D at hlog
  have hlo : Real.exp (-D) ≤ ((normCharacter F T χ x : ℝ≥0) : ℝ) :=
    (Real.le_log_iff_exp_le hpos).mp (abs_le.mp hlog).1
  have hhi : ((normCharacter F T χ x : ℝ≥0) : ℝ) ≤ Real.exp D :=
    (Real.log_le_iff_le_exp hpos).mp (abs_le.mp hlog).2
  constructor
  · apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_inv, coe_expUnit, ← Real.exp_neg] using hlo
  · exact NNReal.coe_le_coe.mp hhi

/-- Bounding a rationally spanning family of normalized character norms above and below
in a split torus gives a compact set of actual principal rational representatives. -/
theorem exists_isCompact_rational_mul_mem_characterBox
    (hT : IsSplitTorus T.toGrp) {S : Set (characterLattice T)}
    (hS : ratSpan S = ⊤) (b : ℝ≥0) :
    ∃ K : Set (AdelicGroupPoints F T.toGrp), IsCompact K ∧
      ∀ x ∈ torusCharacterBox F T S b,
        ∃ q : RationalGroupPoints F T.toGrp, rational F T.toGrp q * x ∈ K := by
  classical
  have : IsAffineHom T.X.hom := hT.isAffineHom
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  let P : Set (intrinsicSubgroup F T) := {a | ∀ χ ∈ S,
    b⁻¹ ≤ (normCharacter F T χ a : ℝ≥0) ∧ (normCharacter F T χ a : ℝ≥0) ≤ b}
  have hP : IsCompact P := isCompact_characterBox F T hT hS b
  obtain ⟨C, hC, hcover⟩ := hasCompactNormOneRationalCover_of_isSplitTorus F T.toGrp hT
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let f : intrinsicSubgroup F T × normOneSubgroup F T.toGrp →
      AdelicGroupPoints F T.toGrp := fun p => p.1.val * p.2.val
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  refine ⟨f '' (P ×ˢ C), (hP.prod hC).image hf, fun x hx => ?_⟩
  let a : intrinsicSubgroup F T :=
    (positiveLogEquiv F T I e).symm (characterLogHom F T.toGrp x)
  have ha : characterLogHom F T.toGrp a.val = characterLogHom F T.toGrp x :=
    (positiveLogEquiv F T I e).apply_symm_apply _
  have hn : a.val⁻¹ * x ∈ normOneSubgroup F T.toGrp := by
    apply (characterLog_eq_zero_iff F T.toGrp _).mp
    change characterLogHom F T.toGrp (a.val⁻¹ * x) = 1
    rw [map_mul, map_inv, ha, inv_mul_cancel]
  let n : normOneSubgroup F T.toGrp := ⟨a.val⁻¹ * x, hn⟩
  have han : a.val * n.val = x := mul_inv_cancel_left _ _
  have haP : a ∈ P := by
    intro χ hχ
    have hnχ : normCharacter F T χ n.val = 1 :=
      (mem_normOneSubgroup F T.toGrp n.val).mp n.property χ.toMul
    have hχeq : normCharacter F T χ a.val = normCharacter F T χ x := by
      rw [← han, map_mul, hnχ, mul_one]
    change b⁻¹ ≤ (normCharacter F T χ a.val : ℝ≥0) ∧
      (normCharacter F T χ a.val : ℝ≥0) ≤ b
    rw [hχeq]
    exact hx χ hχ
  obtain ⟨q, hq⟩ := hcover n
  refine ⟨q, ⟨(a, rationalNormOne F T.toGrp q * n), ⟨haP, hq⟩, ?_⟩⟩
  change a.val * (rational F T.toGrp q * n.val) = rational F T.toGrp q * x
  rw [← han]
  exact mul_left_comm _ _ _

end Langlands.Global.AdelicGroupPoints
