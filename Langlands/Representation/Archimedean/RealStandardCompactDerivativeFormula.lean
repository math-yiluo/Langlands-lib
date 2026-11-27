import Langlands.Global.RankinSelberg.RealStandardCompactSmoothVectors
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealExponentDeformation
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealSmoothRightAction
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # The first-order compact differential formula for real standard modules -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactDifferential

open RealBlockDerivative RealBlockPosition RealJacquetFrobenius
open Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
open RealPrincipalSeriesDuality (contMDiff_mul_fun rightDerivative_mul_fun)

variable {n : ℕ}

local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "I" n:max => matrixModel ℝ n

/-- The coordinate skew matrix `Eᵢⱼ - Eⱼᵢ`. -/
def skewDirection (i j : Fin n) : M n := Matrix.single i j 1 - Matrix.single j i 1

theorem transpose_skewDirection (i j : Fin n) : (skewDirection i j)ᵀ = -skewDirection i j := by
  simp only [skewDirection, Matrix.transpose_sub, Matrix.transpose_single, neg_sub]

/-- A compact directional derivative depends only on the restriction to the compact group. -/
theorem rightDerivative_eq_of_eqOn_skew {f g : G n → ℂ}
    (hf : ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ f) (hg : ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ g)
    (heq : Set.EqOn f g (unitaryCompact ℝ n)) (X : M n) (hX : Xᵀ = -X)
    {k : G n} (hk : k ∈ unitaryCompact ℝ n) :
    rightDerivative (I n) X f k = rightDerivative (I n) X g k := by
  rw [rightDerivative_eq_fderiv hf, rightDerivative_eq_fderiv hg]
  let A : M n := k
  have hA : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  let Y := A * X * star A
  have hY : Y ∈ skewAdjoint (M n) :=
    skewAdjoint.conjugate (skewAdjoint.mem_iff.mpr (by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using hX)) A
  have he : Y * A = A * X := by
    unfold Y
    rw [mul_assoc (A * X), hA, mul_one]
  change fderiv ℝ (unitsExtension f) A (A * X) = fderiv ℝ (unitsExtension g) A (A * X)
  rw [← he]
  exact RealExponentDeformation.fderiv_skew_eq hf hg heq hk hY

private theorem skew_eq_sum (X : M n) (hX : Xᵀ = -X) :
    X = ∑ i, ∑ j, ((1 / 2 : ℝ) * X i j) • skewDirection i j := by
  have hT : (∑ i, ∑ j, Matrix.single j i (X i j)) = Xᵀ := by
    rw [Finset.sum_comm]
    exact Matrix.sum_sum_single (fun i j => X j i)
  have hS : (∑ i, ∑ j, Matrix.single i j (X i j)) = X := Matrix.sum_sum_single X
  calc
    X = (1 / 2 : ℝ) • ∑ i, ∑ j, X i j • skewDirection i j := by
      simp only [skewDirection, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one,
        Finset.sum_sub_distrib]
      rw [hS, hT, hX, ← smul_sub, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
      norm_num
    _ = _ := by simp only [Finset.smul_sum, smul_smul]

private def entryReal (i j : Fin n) : M n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- The restriction of a right matrix derivative to the orthogonal group is a smooth
scalar multiplier plus a sum of the fixed coordinate skew right derivatives with smooth
scalar coefficients. The coefficients work for all vectors of the standard module. -/
def RealStandardCompactDerivativeFormulaStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (X : M n),
    ∃ (c : G n → ℂ) (a : Fin n → Fin n → G n → ℂ),
      ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ c ∧ (∀ i j, ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ (a i j)) ∧
      ∀ (f : realStandardModule n ds) (k : G n), k ∈ unitaryCompact ℝ n →
        rightDerivative (I n) X f.val k = c k * f.val k +
          ∑ i, ∑ j, a i j k * rightDerivative (I n) (skewDirection i j) f.val k

set_option maxHeartbeats 1000000 in
theorem realStandardCompactDerivativeFormula : RealStandardCompactDerivativeFormulaStatement := by
  intro n ds X
  let S (A : M n) := A * X * star A
  let Z (A : M n) := star A * skewPart (S A) * A
  let c (A : M n) := ∑ i, shiftedExponent n ds i * ((upperPart (S A) i i : ℝ) : ℂ)
  let a (i j : Fin n) (A : M n) : ℂ := (((1 / 2 : ℝ) * Z A i j : ℝ) : ℂ)
  have hstar : ContDiff ℝ ∞ (star : M n → M n) := by
    change ContDiff ℝ ∞ (fun A : M n => star A)
    simp_rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap.toContinuousLinearMap.contDiff
  have hS : ContDiff ℝ ∞ S := (contDiff_id.mul contDiff_const).mul hstar
  have hZ : ContDiff ℝ ∞ Z := (hstar.mul (skewPart.contDiff.comp hS)).mul contDiff_id
  have hv : ContMDiff (I n) 𝓘(ℝ, M n) ∞ (fun g : G n => (g : M n)) := Units.contMDiff_val
  have hc : ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ (fun g : G n => c (g : M n)) := by
    unfold c
    refine contMDiff_finsetSum fun i _ => ?_
    have hi : ContDiff ℝ ∞ (fun A : M n =>
        shiftedExponent n ds i * ((upperPart (S A) i i : ℝ) : ℂ)) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        ((entryReal i i).contDiff.comp (upperPart.contDiff.comp hS)))
    exact hi.contMDiff.comp hv
  have ha (i j : Fin n) : ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ (fun g : G n => a i j (g : M n)) :=
    (Complex.ofRealCLM.contDiff.contMDiff).comp
      (((contDiff_const.mul ((entryReal i j).contDiff.comp hZ)).contMDiff).comp hv)
  refine ⟨_, _, hc, ha, fun f k hk => ?_⟩
  let A : M n := k
  have hA : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hA' : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hk
  have hZskew : (Z A)ᵀ = - Z A := by
    have hh := skewAdjoint.mem_iff.mp (skewPart_mem (S A))
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose]
    simp only [Z, star_mul, star_star, hh, mul_neg, neg_mul, mul_assoc]
  have hAZ : A * Z A = skewPart (S A) * A := by
    unfold Z
    rw [← mul_assoc A, ← mul_assoc A, hA', one_mul]
  have hsplit : A * X = upperPart (S A) * A + A * Z A := by
    rw [hAZ, ← add_mul, upperPart_add_skewPart]
    unfold S
    rw [mul_assoc (A * X), hA, mul_one]
  have hF := realStandardModule_le_principalSeries n ds f.property
  let L := fderiv ℝ (unitsExtension f.val) A
  have hu : L (upperPart (S A) * A) = c A * f.val k :=
    fderiv_upperTriangular_of_isExpEquivariant hF.1
      (isExpEquivariant_of_mem_principalSeries (fun i x => realPositionCharacter_exp ds i x) hF)
      k (upperPart_isUpperTriangular _)
  have hsk : L (A * Z A) = ∑ i, ∑ j, a i j A *
      rightDerivative (I n) (skewDirection i j) f.val k := by
    let D := L.comp (ContinuousLinearMap.mul ℝ (M n) A)
    change D (Z A) = _
    have hY (i j : Fin n) : D (skewDirection i j) =
        rightDerivative (I n) (skewDirection i j) f.val k :=
      (rightDerivative_eq_fderiv hF.1 (skewDirection i j) k).symm
    rw [skew_eq_sum (Z A) hZskew, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hY, Complex.real_smul]
  rw [rightDerivative_eq_fderiv hF.1]
  change L (A * X) = _
  rw [hsplit, map_add, hu, hsk]

private def differentiateWord (ds : List RealBlock) (Xs : List (M n))
    (f : realStandardModule n ds) : realStandardModule n ds :=
  Xs.foldr (differentiate ds) f

private theorem iteratedLieDerivative_embed (ds : List RealBlock) (Xs : List (M n))
    (f : realStandardModule n ds) :
    iteratedLieDerivative (I n) (representation (n := n) ds) Xs (embed ds f) =
      embed ds (differentiateWord ds Xs f) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    rw [iteratedLieDerivative_cons, ih, lieDerivative_embed]
    rfl

private theorem rightDerivative_finsetSum {ι : Type*} (s : Finset ι) (V : ι → G n → ℂ)
    (hV : ∀ i, ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ (V i)) (X : M n) :
    rightDerivative (I n) X (fun k => ∑ i ∈ s, V i k) =
      fun k => ∑ i ∈ s, rightDerivative (I n) X (V i) k := by
  let F (i : ι) : SmoothRightAction.smoothFunctions n := ⟨V i, hV i⟩
  let D := rightDerivativeLinearMap (SmoothRightAction.smoothFunctions n)
    (fun _ hf => SmoothRightAction.mem_smoothFunctions.mp hf) X
  have hsum : (∑ i ∈ s, F i).val = fun k => ∑ i ∈ s, V i k := by
    funext k
    simp [F, Finset.sum_apply]
  have hD : D (∑ i ∈ s, F i) = ∑ i ∈ s, D (F i) := map_sum D F s
  change rightDerivative (I n) X (∑ i ∈ s, F i).val = _ at hD
  rw [hsum] at hD
  funext k
  simpa [D, F, rightDerivativeLinearMap, Finset.sum_apply] using congrFun hD k

private theorem exists_wordExpansion (ds : List RealBlock) (Xs : List (M n)) :
    ∃ (ι : Type) (inst : Fintype ι) (w : ι → List (M n)) (a : ι → G n → ℂ),
      letI := inst
      (∀ i, ∀ Y ∈ w i, Yᵀ = -Y) ∧
      (∀ i, ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ (a i)) ∧
      ∀ (f : realStandardModule n ds) (k : G n), k ∈ unitaryCompact ℝ n →
        (differentiateWord ds Xs f).val k =
          ∑ i, a i k * (differentiateWord ds (w i) f).val k := by
  classical
  induction Xs with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ => [], fun _ _ => 1, by simp,
      fun _ => contMDiff_const, by simp⟩
  | cons X Xs ih =>
    obtain ⟨ι, inst, w, a, hw, ha, he⟩ := ih
    let _ : Fintype ι := inst
    obtain ⟨c, b, hc, hb, hX⟩ := realStandardCompactDerivativeFormula n ds X
    let Z (p : Fin n × Fin n) := skewDirection p.1 p.2
    let B (p : Fin n × Fin n) := b p.1 p.2
    let u : ι ⊕ (ι × (Fin n × Fin n)) → List (M n) :=
      Sum.elim w (fun ip => Z ip.2 :: w ip.1)
    let A : ι ⊕ (ι × (Fin n × Fin n)) → G n → ℂ :=
      Sum.elim
        (fun i k => c k * a i k + ∑ p, B p k * rightDerivative (I n) (Z p) (a i) k)
        (fun ip k => B ip.2 k * a ip.1 k)
    refine ⟨_, inferInstance, u, A, ?_, ?_, ?_⟩
    · rintro (i | ⟨i, p⟩) Y hY
      · exact hw i Y hY
      · rcases List.mem_cons.mp hY with rfl | hy
        · exact transpose_skewDirection _ _
        · exact hw i Y hy
    · rintro (i | ⟨i, p⟩)
      · exact (contMDiff_mul_fun hc (ha i)).add (contMDiff_finsetSum fun p _ =>
          contMDiff_mul_fun (hb p.1 p.2) (contMDiff_rightDerivative (ha i) (Z p)))
      · exact contMDiff_mul_fun (hb p.1 p.2) (ha i)
    · intro f k hk
      let g := differentiateWord ds Xs f
      let H (i : ι) := (differentiateWord ds (w i) f).val
      let F (i : ι) (k : G n) := a i k * H i k
      have hH (i : ι) : ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ (H i) :=
        (differentiateWord ds (w i) f).property.1.1
      have hF (i : ι) : ContMDiff (I n) 𝓘(ℝ, ℂ) ∞ (F i) := contMDiff_mul_fun (ha i) (hH i)
      have hsum : Set.EqOn g.val (fun k => ∑ i, F i k) (unitaryCompact ℝ n) :=
        fun x hx => he f x hx
      have hZ (p : Fin n × Fin n) : (Z p)ᵀ = -Z p := transpose_skewDirection _ _
      have hD (p : Fin n × Fin n) : rightDerivative (I n) (Z p) g.val k =
          ∑ i, (rightDerivative (I n) (Z p) (a i) k * H i k +
            a i k * rightDerivative (I n) (Z p) (H i) k) := by
        rw [rightDerivative_eq_of_eqOn_skew g.property.1.1
          (contMDiff_finsetSum fun i _ => hF i) hsum (Z p) (hZ p) hk,
          rightDerivative_finsetSum Finset.univ F hF (Z p)]
        exact Finset.sum_congr rfl fun i _ => rightDerivative_mul_fun (ha i) (hH i) (Z p) k
      have hX' : rightDerivative (I n) X g.val k = c k * g.val k +
          ∑ p, B p k * rightDerivative (I n) (Z p) g.val k := by
        rw [Fintype.sum_prod_type]
        exact hX g k hk
      change rightDerivative (I n) X g.val k =
          ∑ i, A i k * (differentiateWord ds (u i) f).val k
      rw [hX', hsum hk]
      simp_rw [hD, Finset.mul_sum]
      rw [Finset.sum_comm (γ := Fin n × Fin n) (α := ι), ← Finset.sum_add_distrib]
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type (fun ip : ι × (Fin n × Fin n) =>
        A (Sum.inr ip) k * (differentiateWord ds (u (Sum.inr ip)) f).val k)]
      simp only [A, u, Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      change c k * (a i k * H i k) + (∑ p, B p k *
          (rightDerivative (I n) (Z p) (a i) k * H i k +
            a i k * rightDerivative (I n) (Z p) (H i) k)) =
          (c k * a i k + ∑ p, B p k * rightDerivative (I n) (Z p) (a i) k) * H i k +
            ∑ p, B p k * a i k * rightDerivative (I n) (Z p) (H i) k
      simp only [add_mul, Finset.sum_mul, mul_add]
      rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun p _ => by ring

/-- The compact-direction word estimate for every genuine smooth vector in the
compact Banach realization of a real standard module. -/
theorem exists_compactWordBound (ds : List RealBlock) (Xs : List (M n)) :
    ∃ (T : Finset (List (M n))) (C : ℝ),
      0 ≤ C ∧ (∀ w ∈ T, ∀ Y ∈ w, Yᵀ = -Y) ∧
      ∀ v : smoothVectors (I n) (representation (n := n) ds),
        ‖iteratedLieDerivative (I n) (representation (n := n) ds) Xs v‖ ≤
          C * ∑ w ∈ T, ‖iteratedLieDerivative (I n) (representation (n := n) ds) w v‖ := by
  classical
  obtain ⟨ι, inst, w, a, hw, ha, he⟩ := exists_wordExpansion ds Xs
  let _ : Fintype ι := inst
  let T := Finset.univ.image w
  let A (i : ι) : C(Matrix.unitaryGroup (Fin n) ℝ, ℂ) :=
    ⟨fun k => a i (Unitary.toUnits k), (ha i).continuous.comp continuous_unitary_toUnits⟩
  refine ⟨T, ∑ i, ‖A i‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_, ?_⟩
  · intro W hW
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
    exact hw i
  · intro v
    obtain ⟨f, rfl⟩ := (smoothEquiv ds).surjective v
    simp only [smoothEquiv_val, iteratedLieDerivative_embed]
    let N (W : List (M n)) := ‖embed ds (differentiateWord ds W f)‖
    have hN : 0 ≤ ∑ W ∈ T, N W := Finset.sum_nonneg fun _ _ => norm_nonneg _
    change ‖compactRestriction ds (differentiateWord ds Xs f)‖ ≤
      (∑ i, ‖A i‖) * ∑ W ∈ T, N W
    refine (ContinuousMap.norm_le _ (mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hN)).mpr
      fun k => ?_
    rw [compactRestriction_apply, he f (Unitary.toUnits k) k.property, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    have heval : ‖(differentiateWord ds (w i) f).val (Unitary.toUnits k)‖ ≤ N (w i) :=
      (compactRestriction ds (differentiateWord ds (w i) f)).norm_coe_le_norm k
    have hmem : w i ∈ T := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hi : N (w i) ≤ ∑ W ∈ T, N W :=
      Finset.single_le_sum (fun W _ => norm_nonneg (embed ds (differentiateWord ds W f))) hmem
    exact mul_le_mul ((A i).norm_coe_le_norm k) (heval.trans hi) (norm_nonneg _) (norm_nonneg _)

end Langlands.Archimedean.RealStandardCompactDifferential
