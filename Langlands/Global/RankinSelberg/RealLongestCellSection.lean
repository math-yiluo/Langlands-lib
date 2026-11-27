import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerUniqueness
import Langlands.Group.GL.RealBruhatTrailingChart

/-! # Phased real inducing sections on the longest cell -/

noncomputable section

open Filter Set TopologicalSpace Metric
open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator Pointwise Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealLongestCellSection

open RealBruhatTrailingChart RealJacquetFrobenius RealPrincipalSeriesDistribution
open RealPrincipalSeriesWhittakerUniqueness

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "W" => weylLong (r + 1) ℝ
local notation "O" => longestBruhatCell ℝ r

/-- A point of the longest cell has an actual Borel and upper-unipotent factorization. -/
theorem mem_longestCell_iff (x : G) :
    x.val ∈ O ↔ ∃ (b : B) (v : U), x = b.val * W * v.val := by
  have h (b : B) (v : U) : (orbitHomeomorph (b, v⁻¹)).val = (b.val * W * v.val).val := by
    rw [orbitHomeomorph_val]
    simp only [matrixAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.comp_apply,
      LinearMap.mulRight_apply, LinearMap.mulLeft_apply, inv_inv, Units.val_mul]
  constructor
  · intro hx
    obtain ⟨⟨b, v⟩, hv⟩ := orbitHomeomorph.surjective (⟨x.val, hx⟩ : O)
    refine ⟨b, v⁻¹, Units.ext ?_⟩
    simpa only [inv_inv, hv] using h b v⁻¹
  · rintro ⟨b, v, rfl⟩
    rw [← h]
    exact (orbitHomeomorph (b, v⁻¹)).property

private theorem longestCell_leftBorel (b : B) (x : G) : (b.val * x).val ∈ O ↔ x.val ∈ O := by
  simp only [mem_longestCell_iff]
  constructor
  · rintro ⟨c, v, h⟩
    refine ⟨b⁻¹ * c, v, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left] using
      congrArg ((b.val)⁻¹ * ·) h
  · rintro ⟨c, v, rfl⟩
    exact ⟨b * c, v, by simp only [Subgroup.coe_mul, mul_assoc]⟩

private def coordinates (x : M) : M := (trailingChart (r + 1)).symm (x * (W).val)

private def leftFactor (x : M) : M := upperProjection (r + 1) (coordinates x)

private def rightFactor (x : M) : M :=
  (W).val * lowerFactorOfCoordinates (coordinates x) * (W).val

private theorem factors_on_orbit (b : B) (v : U) :
    leftFactor (b.val * W * v.val).val = b.val.val ∧
    rightFactor (b.val * W * v.val).val = v.val.val := by
  let l : M := (W * v.val * W).val
  let z : M := b.val.val + (l - 1)
  have hl (i j : Fin (r + 1)) (hij : i < j) : l i j = 0 := by
    rw [show l i j = (W * v.val * W) i j from rfl, weylLong_conjugate_entry]
    exact UpperUnipotent.entry_eq_zero v (Fin.rev_lt_rev.mpr hij)
  have hl₁ (i : Fin (r + 1)) : l i i = 1 := by
    rw [show l i i = (W * v.val * W) i i from rfl, weylLong_conjugate_entry]
    exact v.property.2 _
  have hUpper : upperProjection (r + 1) z = b.val.val := by
    ext i j
    by_cases hij : j < i
    · rw [upperProjection_apply, ite_eq_left hij, b.property hij]
    · rw [upperProjection_apply, ite_eq_right hij]
      change b.val.val i j + (l i j - (1 : M) i j) = _
      rcases eq_or_lt_of_le (le_of_not_gt hij) with h | h
      · subst j
        simp [hl₁]
      · simp [hl _ _ h, h.ne]
  have hLower : lowerFactorOfCoordinates z = l := by
    rw [lowerFactorOfCoordinates, hUpper]
    dsimp only [z]
    abel
  have hz : z ∈ (trailingChart (r + 1)).source := by
    change ∀ i, z i i ≠ 0
    intro i
    simpa [z, hl₁] using diag_ne_zero b.property b.val.isUnit i
  have hx : (trailingChart (r + 1)) z = (b.val * W * v.val).val * (W).val := by
    change upperProjection (r + 1) z * lowerFactorOfCoordinates z = _
    rw [hUpper, hLower]
    simp only [l, Units.val_mul, mul_assoc]
  have heq : coordinates (b.val * W * v.val).val = z := by
    unfold coordinates
    rw [← hx]
    exact (trailingChart (r + 1)).left_inv hz
  refine ⟨by rw [leftFactor, heq, hUpper], ?_⟩
  rw [rightFactor, heq, hLower]
  change (W * (W * v.val * W) * W).val = _
  have he : W * (W * v.val * W) * W = (W * W) * v.val * (W * W) := by group
  rw [he, weylLong_mul_self, one_mul, mul_one]

private theorem contDiffAt_coordinates {x : M} (hx : x ∈ O) : ContDiffAt ℝ ∞ coordinates x := by
  obtain ⟨g, hg, rfl⟩ := hx
  have ht : g.val * (W).val ∈ trailingDomain (r + 1) := mem_trailingDomain_of_mem_cell Fin.revPerm hg
  exact ((contDiffOn_trailingChart_symm (r + 1)).contDiffAt
    ((isOpen_trailingDomain _).mem_nhds ht)).comp g.val (contDiffAt_id.mul contDiffAt_const)

private def matrixPhase (a : ℝˣ) (x : M) : ℂ :=
  (realScaledCharacter a).complex (∑ i : Fin r, x i.castSucc i.succ)

private theorem contDiff_matrixPhase (a : ℝˣ) : ContDiff ℝ ∞ (matrixPhase (r := r) a) := by
  have hSum : ContDiff ℝ ∞ (fun x : M => ∑ i : Fin r, x i.castSucc i.succ) :=
    ContDiff.sum fun i _ => (Matrix.entryLinearMap ℝ ℝ i.castSucc i.succ).toContinuousLinearMap.contDiff
  change ContDiff ℝ ∞ (fun x : M => (realScaledCharacter a).complex (∑ i : Fin r, x i.castSucc i.succ))
  simp only [UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply, Real.fourierChar_apply]
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_const.mul hSum))).mul
    contDiff_const).cexp

/-- A character inducing function has its topological support in the longest cell and its
restriction to the long Weyl orbit is the Whittaker phase times a nonnegative compact bump. -/
def RealLongestCellSectionStatement : Prop :=
  ∀ (n : ℕ) (s : Fin (n + 1) → ℂ) (e : Fin (n + 1) → Fin 2) (a : ℝˣ),
    ∃ (F : principalSeries ℝ (n + 1) (posChar s e))
      (κ : Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ → ℝ),
      HasCompactSupport κ ∧ (∀ v, 0 ≤ κ v) ∧ κ 1 = 1 ∧
      tsupport F.val ⊆ Units.val ⁻¹' (longestBruhatCell ℝ n : Set _) ∧
      ∀ v, F.val (weylLong (n + 1) ℝ * v.val) = realWhittakerCharacter a v.val * (κ v : ℂ)

set_option maxHeartbeats 650000 in
private theorem exists_phasedSection (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2) (a : ℝˣ) :
    ∃ (F : principalSeries ℝ (r + 1) (posChar s e)) (κ : U → ℝ),
      HasCompactSupport κ ∧ (∀ v, 0 ≤ κ v) ∧ κ 1 = 1 ∧
      tsupport F.val ⊆ Units.val ⁻¹' (O : Set M) ∧
      ∀ v, F.val (W * v.val) = realWhittakerCharacter a v.val * (κ v : ℂ) := by
  classical
  have hOpen : IsOpen {X : M | IsUnit X} := isOpen_setOf_isUnit_matrix
  obtain ⟨δ, hδ, hδU⟩ := nhds_basis_closedBall.mem_iff.mp
    (hOpen.mem_nhds (show (1 : M) ∈ {X : M | IsUnit X} from isUnit_one))
  let β : ContDiffBump (1 : M) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let κ (v : U) : ℝ := β v.val.val
  let C : Set U := (fun v : U => v.val.val) ⁻¹' Metric.closedBall (1 : M) δ
  have hC : IsCompact C := (UpperUnipotent.isClosed (n := r + 1) (R := ℝ)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (RealGodement.isCompact_val_preimage (isCompact_closedBall _ _) fun _ hx => hδU hx)
  have hκ : Function.support κ ⊆ C := by
    intro v hv
    by_contra hout
    apply hv
    exact β.zero_of_le_dist (not_le.mp hout).le
  let K : Set G := (fun v : U => W * v.val) '' C
  have hK : IsCompact K := hC.image (continuous_const.mul continuous_subtype_val)
  let S : Set G := (B : Set G) * K
  have hS : IsClosed S := (isClosed_upperTriangularSubgroup _ _).mul_right_of_isCompact hK
  have hSO : S ⊆ Units.val ⁻¹' O := by
    rintro _ ⟨b, hb, _, ⟨v, _, rfl⟩, rfl⟩
    exact (mem_longestCell_iff _).2 ⟨⟨b, hb⟩, v, (mul_assoc _ _ _).symm⟩
  let J (x : M) : ℂ := diagChar s e (leftFactor x) * matrixPhase a (rightFactor x) *
    (β (rightFactor x) : ℂ)
  let F (g : G) : ℂ := if g.val ∈ O then J g.val else 0
  have hOrbit (b : B) (v : U) : F (b.val * W * v.val) =
      (positionBorelCharacter s e b : ℂ) * (realWhittakerCharacter a v.val * (κ v : ℂ)) := by
    have hf := factors_on_orbit b v
    have hmem := (mem_longestCell_iff _).2 ⟨b, v, rfl⟩
    change (if (b.val * W * v.val).val ∈ O then _ else _) = _
    rw [ite_eq_left hmem]
    change diagChar s e (leftFactor _) * matrixPhase a (rightFactor _) * (β (rightFactor _) : ℂ) = _
    rw [hf.1, hf.2, positionBorelCharacter_val, mul_assoc]
    rfl
  have hSupport : tsupport F ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    have hmem : x.val ∈ O := by
      by_contra hn
      exact hx (ite_eq_right hn)
    obtain ⟨b, v, rfl⟩ := (mem_longestCell_iff _).1 hmem
    have hv : v ∈ Function.support κ := by
      intro hz
      apply hx
      rw [hOrbit, hz, Complex.ofReal_zero, mul_zero, mul_zero]
    exact ⟨b.val, b.property, W * v.val, ⟨v, hκ hv, rfl⟩, (mul_assoc _ _ _).symm⟩
  have hSmooth : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ F := by
    intro x
    by_cases hx : x.val ∈ O
    · obtain ⟨b, v, rfl⟩ := (mem_longestCell_iff _).1 hx
      let y : M := (b.val * W * v.val).val
      have hCrd : ContDiffAt ℝ ∞ coordinates y := contDiffAt_coordinates hx
      have hLeft : ContDiffAt ℝ ∞ leftFactor y :=
        (upperProjection (r + 1)).contDiff.contDiffAt.comp y hCrd
      have hRight : ContDiffAt ℝ ∞ rightFactor y :=
        (contDiffAt_const.mul (contDiffAt_const.add (hCrd.sub hLeft))).mul contDiffAt_const
      have hdiag (i : Fin (r + 1)) : leftFactor y i i ≠ 0 := by
        rw [(factors_on_orbit b v).1]
        exact diag_ne_zero b.property b.val.isUnit i
      have hJ : ContDiffAt ℝ ∞ J y :=
        (((contDiffAt_diagChar s e hdiag).comp y hLeft).mul
          ((contDiff_matrixPhase a).contDiffAt.comp y hRight)).mul
          (Complex.ofRealCLM.contDiff.contDiffAt.comp y (β.contDiff.contDiffAt.comp y hRight))
      refine (hJ.comp_contMDiffAt (Units.contMDiff_val (b.val * W * v.val))).congr_of_eventuallyEq ?_
      have h : ∀ᶠ z : G in 𝓝 (b.val * W * v.val), z.val ∈ O :=
        (O).isOpen.preimage Units.continuous_val |>.mem_nhds hx
      exact h.mono fun z hz => ite_eq_left hz
    · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      have h : ∀ᶠ z in 𝓝 x, z ∉ S := hS.isOpen_compl.mem_nhds (fun h => hx (hSO h))
      exact h.mono fun z hz => image_eq_zero_of_notMem_tsupport (fun h => hz (hSupport h))
  have hCov (b : B) (x : G) : F (b.val * x) = (positionBorelCharacter s e b : ℂ) * F x := by
    by_cases hx : x.val ∈ O
    · obtain ⟨c, v, rfl⟩ := (mem_longestCell_iff _).1 hx
      have he : b.val * (c.val * W * v.val) = (b * c).val * W * v.val := by
        simp only [Subgroup.coe_mul, mul_assoc]
      rw [he, hOrbit, hOrbit, map_mul, Units.val_mul, mul_assoc]
    · have hy := mt (longestCell_leftBorel b x).mp hx
      change (if (b.val * x).val ∈ O then _ else _) = _
      rw [ite_eq_right hy, show F x = 0 from ite_eq_right hx, mul_zero]
  refine ⟨⟨F, hSmooth, fun d u x => ?_⟩, κ, HasCompactSupport.of_support_subset_isCompact hC hκ,
    fun _ => β.nonneg, ?_, hSupport.trans hSO, ?_⟩
  · exact (hCov (diagonalUnipotentInBorel d u) x).trans (by rw [positionBorelCharacter_diagonalUnipotent])
  · exact β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
  · intro v
    simpa only [Subgroup.coe_one, one_mul, map_one, Units.val_one] using hOrbit 1 v

theorem realLongestCellSection : RealLongestCellSectionStatement :=
  fun _ => exists_phasedSection

end Langlands.Global.RankinSelbergGlobal.RealLongestCellSection
