import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRootDerivative
import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Langlands.Group.GL.UpperTriangularMaximalSolvable
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization

/-! # Character-detecting stabilizer paths on the nonopen Bruhat cells -/

noncomputable section

open scoped Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open Langlands.GeneralLinear UpperBruhatCoordinates UpperTriangularMaximalSolvable OppositeRootNonsolvable
open Langlands.LocalFactor.Archimedean (complexScaledCharacter complexScaledCharacter_apply)
open Langlands.Whittaker.UpperUnipotentCharacter (upperTransvection)
open ComplexLocalConvergence (simpleRootDirection rootCharacterDerivative)

variable {r : ℕ}
local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "U" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "B" => upperTriangularSubgroup n ℂ
local notation "M" => Matrix (Fin n) (Fin n) ℂ

private theorem exists_adjacent_ascent (w : Equiv.Perm (Fin n)) (hw : w ≠ Fin.revPerm) :
    ∃ i : Fin r, w i.castSucc < w i.succ := by
  by_contra! h
  have ha : StrictAnti w := Fin.strictAnti_iff_succ_lt.mpr fun i =>
    lt_of_le_of_ne (h i) (w.injective.ne i.castSucc_lt_succ.ne.symm)
  let e : Equiv.Perm (Fin n) := w.trans Fin.revPerm
  have hm : Monotone e := by
    intro i j hij
    exact Fin.rev_le_rev.mpr (ha.antitone hij)
  have he := e.monotone_iff.mp hm
  apply hw
  apply Equiv.ext
  intro i
  apply Fin.rev_injective
  have hi := congrArg (fun v : Equiv.Perm (Fin n) => v i) he
  change (w i).rev = i at hi
  simpa only [Fin.revPerm_apply, Fin.rev_rev] using hi

private theorem upper_diag_mul {A C : M} (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular)
    (i : Fin n) : (A * C) i i = A i i * C i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hj | hj
  · rw [hA hj, zero_mul]
  · rw [hC hj, mul_zero]

private theorem conjugate_mem_upperUnipotent (b : B) {u : G} (hu : u ∈ U) :
    b.val * u * b.val⁻¹ ∈ U := by
  have hb : b.val.val.IsUpperTriangular := b.2
  have hb' : (b.val⁻¹).val.IsUpperTriangular := (b⁻¹).2
  refine ⟨(hb.mul hu.1).mul hb', fun i => ?_⟩
  change ((b.val.val * u.val) * b.val⁻¹.val) i i = 1
  rw [upper_diag_mul (hb.mul hu.1) hb', upper_diag_mul hb hu.1, hu.2 i, mul_one,
    ← upper_diag_mul hb hb', Units.mul_inv, Matrix.one_apply_eq]

private def rootPath (a : ℂˣ) (i : Fin r) (t : ℝ) : U :=
  upperTransvection i.castSucc i.succ i.castSucc_lt_succ ((t : ℂ) * (a : ℂ)⁻¹)

private theorem rootPath_val (a : ℂˣ) (i : Fin r) (t : ℝ) :
    (rootPath a i t).val.val = 1 + t • simpleRootDirection a i := by
  change 1 + Matrix.single i.castSucc i.succ ((t : ℂ) * (a : ℂ)⁻¹) = _
  ext j k
  simp [simpleRootDirection, Matrix.single_apply, Complex.real_smul]

private theorem rootPath_neg (a : ℂˣ) (i : Fin r) (t : ℝ) :
    (rootPath a i (-t)).val = (rootPath a i t).val⁻¹ := by
  change transvectionUnit _ _ i.castSucc_lt_succ.ne ((↑(-t) : ℂ) * (a : ℂ)⁻¹) =
    (transvectionUnit _ _ i.castSucc_lt_succ.ne ((↑t : ℂ) * (a : ℂ)⁻¹))⁻¹
  rw [transvection_inv, Complex.ofReal_neg, neg_mul]

private theorem rootPath_character (a : ℂˣ) (i : Fin r) (t : ℝ) :
    complexWhittakerCharacter a (rootPath a i t).val = Complex.exp ((t : ℂ) * rootCharacterDerivative) := by
  have hentry (j : Fin r) : (rootPath a i t).val.val j.castSucc j.succ =
      if j = i then (t : ℂ) * (a : ℂ)⁻¹ else 0 := by
    change (1 + Matrix.single i.castSucc i.succ ((t : ℂ) * (a : ℂ)⁻¹) : M) j.castSucc j.succ = _
    simp [Matrix.one_apply_ne j.castSucc_lt_succ.ne, Matrix.single_apply, eq_comm (a := i) (b := j)]
  unfold complexWhittakerCharacter
  simp_rw [hentry]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)]
  change (complexScaledCharacter a ((t : ℂ) * (a : ℂ)⁻¹) : ℂ) = _
  rw [complexScaledCharacter_apply, mul_left_comm, mul_inv_cancel₀ a.ne_zero, mul_one,
    Algebra.trace_complex_apply, Complex.ofReal_re, Real.fourierChar_apply]
  congr 1
  unfold rootCharacterDerivative
  push_cast
  ring

private theorem character_conjugate (a : ℂˣ) (u v : U) :
    complexWhittakerCharacter a (v⁻¹ * u * v).val = complexWhittakerCharacter a u.val := by
  unfold complexWhittakerCharacter
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [UpperUnipotent.mul_adjacent_entry, UpperUnipotent.inv_adjacent_entry]
  abel

private def conjugateMatrix (q : G) (X : M) : M := q.val * X * q⁻¹.val

private theorem conjugateMatrix_sq (q : G) (X : M) (hX : X * X = 0) :
    conjugateMatrix q X * conjugateMatrix q X = 0 := by
  calc
    _ = q.val * (X * (q⁻¹.val * q.val) * X) * q⁻¹.val := by unfold conjugateMatrix; noncomm_ring
    _ = 0 := by rw [Units.inv_mul, mul_one, hX, mul_zero, zero_mul]

private theorem conjugate_rootPath_val (q : G) (a : ℂˣ) (i : Fin r) (t : ℝ) :
    (q * (rootPath a i t).val * q⁻¹).val = 1 + t • conjugateMatrix q (simpleRootDirection a i) := by
  simp only [Units.val_mul, rootPath_val, conjugateMatrix, mul_add, add_mul, mul_one, Matrix.mul_smul,
    Matrix.smul_mul, Units.mul_inv]

/-- Every non-long upper Bruhat cell has stabilizer paths of upper-unipotent pairs with
square-zero directions. The right path detects the nontrivial trace character. -/
def ComplexJacquetBoundaryStabilizerStatement : Prop :=
  ∀ (a : ℂˣ) (w : Equiv.Perm (Fin n)), w ≠ Fin.revPerm →
    ∀ g ∈ upperBruhatCell n ℂ w,
    ∃ (X Y : M) (l u : ℝ → U), X * X = 0 ∧ Y * Y = 0 ∧ ∀ t : ℝ,
      (l t).val.val = 1 + t • X ∧ (u t).val.val = 1 + t • Y ∧
      (l t).val * g * (u t).val = g ∧
      complexWhittakerCharacter a (u t).val = Complex.exp ((t : ℂ) * rootCharacterDerivative)

set_option maxHeartbeats 600000 in
theorem complexJacquetBoundaryStabilizer : ComplexJacquetBoundaryStabilizerStatement (r := r) := by
  intro a w hw g hg
  obtain ⟨i, hi⟩ := exists_adjacent_ascent w hw
  obtain ⟨⟨b, v⟩, hv⟩ := upperBruhatCellMap_surjective w ⟨g, hg⟩
  let p := permutation n ℂ w
  let V : U := ⟨v.val, permutationUnipotentMinus_le_upperUnipotent n ℂ w v.2⟩
  have hgv : b.val * p * V.val = g := congrArg Subtype.val hv
  let Z := simpleRootDirection a i
  have hZ : Z * Z = 0 := Matrix.single_mul_single_of_ne _ _ _ _ i.castSucc_lt_succ.ne.symm _
  let l (t : ℝ) : U := ⟨b.val * (p * (rootPath a i (-t)).val * p⁻¹) * b.val⁻¹, by
    apply conjugate_mem_upperUnipotent b
    change permutation n ℂ w * transvectionUnit _ _ i.castSucc_lt_succ.ne _ *
      (permutation n ℂ w)⁻¹ ∈ U
    rw [permutation_conjugate_transvection]
    exact (upperTransvection _ _ hi _).2⟩
  let u (t : ℝ) : U := V⁻¹ * rootPath a i t * V
  refine ⟨-conjugateMatrix (b.val * p) Z, conjugateMatrix V.val⁻¹ Z, l, u, ?_,
    conjugateMatrix_sq _ _ hZ, fun t => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [neg_mul, mul_neg, conjugateMatrix_sq _ _ hZ, neg_zero, neg_zero]
  · have h : (l t).val = (b.val * p) * (rootPath a i (-t)).val * (b.val * p)⁻¹ := by
      change b.val * (p * (rootPath a i (-t)).val * p⁻¹) * b.val⁻¹ = _
      group
    rw [h, conjugate_rootPath_val, neg_smul, smul_neg]
  · change (V.val⁻¹ * (rootPath a i t).val * (V.val⁻¹)⁻¹).val = _
    exact conjugate_rootPath_val _ _ _ _
  · rw [← hgv]
    change b.val * (p * (rootPath a i (-t)).val * p⁻¹) * b.val⁻¹ *
      (b.val * p * V.val) * (V.val⁻¹ * (rootPath a i t).val * V.val) = _
    rw [rootPath_neg]
    group
  · exact (character_conjugate a _ _).trans (rootPath_character a i t)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
