import Langlands.LinearAlgebra.DominantTriangularInvariants
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Determinant

/-! # Simple reflections, the deletion lemma and strictly dominant stabilizers -/

noncomputable section

open Set Function

namespace Langlands.LinearAlgebra.WeylCharacter

open DominantTriangular

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} (b : P.Base)

/-! ### Positive roots -/

theorem positiveCone_eq_closure_image :
    positiveCone P b = AddSubmonoid.closure (P.root '' b.support) := by
  rw [Set.image_eq_range]
  rfl

theorem root_mem_or_neg_mem (i : ι) :
    P.root i ∈ positiveCone P b ∨ -P.root i ∈ positiveCone P b := by
  rw [positiveCone_eq_closure_image]
  exact b.root_mem_or_neg_mem i

theorem neg_root_notMem_of_mem {i : ι} (hi : P.root i ∈ positiveCone P b) :
    -P.root i ∉ positiveCone P b := fun h =>
  P.ne_zero i (eq_zero_of_mem_positiveCone_of_neg_mem P b hi h)

theorem neg_root_mem_iff (i : ι) :
    -P.root i ∈ positiveCone P b ↔ P.root i ∉ positiveCone P b :=
  ⟨fun h hi => neg_root_notMem_of_mem b hi h,
    fun h => (root_mem_or_neg_mem b i).resolve_left h⟩

/-- Membership of a root in the positive cone is Mathlib's positivity `b.IsPos`. -/
theorem isPos_iff_mem (i : ι) : b.IsPos i ↔ P.root i ∈ positiveCone P b := by
  classical
  have hsum : ∀ f : ι → ℕ, ∑ j ∈ b.support, f j • P.root j ∈ positiveCone P b := fun f =>
    sum_mem fun j hj => AddSubmonoid.nsmul_mem _ (root_mem_positiveCone P b ⟨j, hj⟩) _
  obtain ⟨f, -, hf | hf⟩ := b.exists_root_eq_sum_nat_or_neg i
  · have hf' : P.root i = ∑ j ∈ b.support, (f j : ℤ) • P.root j := by
      rw [hf]
      exact Finset.sum_congr rfl fun j _ => (natCast_zsmul _ _).symm
    refine iff_of_true ?_ (hf ▸ hsum f)
    rw [RootPairing.Base.isPos_iff', RootPairing.Base.height_eq_sum hf']
    exact Finset.sum_nonneg fun j _ => Int.natCast_nonneg _
  · have hf' : P.root i = ∑ j ∈ b.support, (-(f j : ℤ)) • P.root j := by
      rw [hf, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [neg_smul, natCast_zsmul]
    refine iff_of_false ?_ ?_
    · rw [RootPairing.Base.isPos_iff, RootPairing.Base.height_eq_sum hf', not_lt]
      exact Finset.sum_nonpos fun j _ => neg_nonpos.mpr (Int.natCast_nonneg _)
    · rw [← neg_root_mem_iff, hf, neg_neg]
      exact hsum f

theorem root_reflectionPerm_self_notMem {a : ι} (ha : a ∈ b.support) :
    P.root (P.reflectionPerm a a) ∉ positiveCone P b := by
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  exact neg_root_notMem_of_mem b (root_mem_positiveCone P b ⟨a, ha⟩)

variable [Finite ι] [P.IsReduced]

/-- A simple reflection maps every positive root other than its own simple root to a
positive root. -/
theorem reflection_root_mem_of_ne {a i : ι} (ha : a ∈ b.support)
    (hi : P.root i ∈ positiveCone P b) (hia : i ≠ a) :
    P.reflection a (P.root i) ∈ positiveCone P b := by
  rw [← RootPairing.root_reflectionPerm, ← isPos_iff_mem]
  exact ((isPos_iff_mem b i).mpr hi).reflectionPerm ha hia

theorem root_reflectionPerm_mem_iff {a i : ι} (ha : a ∈ b.support) (hia : i ≠ a)
    (hia' : i ≠ P.reflectionPerm a a) :
    P.root (P.reflectionPerm a i) ∈ positiveCone P b ↔ P.root i ∈ positiveCone P b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hne : P.reflectionPerm a i ≠ a := by
      intro h'
      have h'' := congrArg (P.reflectionPerm a) h'
      rw [RootPairing.reflectionPerm_self] at h''
      exact hia' h''
    have := reflection_root_mem_of_ne b ha h hne
    rwa [← RootPairing.root_reflectionPerm, RootPairing.reflectionPerm_self] at this
  · rw [RootPairing.root_reflectionPerm]
    exact reflection_root_mem_of_ne b ha h hia

omit [Finite ι] [P.IsReduced] in
/-- Conjugating a root reflection by an element of the reflection group. -/
theorem mul_reflection_mul_inv {w : M ≃ₗ[ℤ] M} (hw : w ∈ reflectionGroup P) {i j : ι}
    (h : w (P.root i) = P.root j) : w * P.reflection i * w⁻¹ = P.reflection j := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_mem_reflectionGroup hw
  have hj : σ i = j := P.root.injective ((hσ i).1.symm.trans h)
  ext x
  have h2 : P.coroot' i (w.symm x) = P.coroot' j x := by
    rw [← hj, ← (hσ i).2 (w.symm x), LinearEquiv.apply_symm_apply]
  change w (P.reflection i (w.symm x)) = P.reflection j x
  rw [RootPairing.reflection_apply, RootPairing.reflection_apply, map_sub, map_smul,
    LinearEquiv.apply_symm_apply, h, h2]

omit [Finite ι] [P.IsReduced] in
@[simp]
theorem reflection_mul_self (i : ι) : P.reflection i * P.reflection i = 1 :=
  LinearEquiv.ext fun x => P.reflection_same i x

/-! ### Words in the simple reflections -/

/-- The product of the simple reflections along a list of simple indices. -/
def word (L : List b.support) : M ≃ₗ[ℤ] M :=
  (L.map fun a => P.reflection (a : ι)).prod

omit [Finite ι] [P.IsReduced] in
@[simp]
theorem word_nil : word b [] = 1 := rfl

omit [Finite ι] [P.IsReduced] in
@[simp]
theorem word_cons (a : b.support) (L : List b.support) :
    word b (a :: L) = P.reflection a * word b L := by
  simp [word]

omit [Finite ι] [P.IsReduced] in
theorem word_append (L L' : List b.support) : word b (L ++ L') = word b L * word b L' := by
  simp [word]

omit [Finite ι] [P.IsReduced] in
theorem word_concat (L : List b.support) (a : b.support) :
    word b (L ++ [a]) = word b L * P.reflection a := by
  simp [word]

omit [Finite ι] [P.IsReduced] in
theorem word_reverse (L : List b.support) : word b L.reverse = (word b L)⁻¹ := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.reverse_cons, word_concat, ih, word_cons, mul_inv_rev, RootPairing.reflection_inv]

omit [Finite ι] [P.IsReduced] in
theorem word_mem (L : List b.support) : word b L ∈ reflectionGroup P := by
  induction L with
  | nil => exact one_mem _
  | cons a L ih =>
    rw [word_cons]
    exact mul_mem (reflection_mem_reflectionGroup P a) ih

theorem exists_word_eq_reflection (i : ι) :
    ∃ L : List b.support, word b L = P.reflection i := by
  refine b.induction_reflect i (p := fun i => ∃ L : List b.support, word b L = P.reflection i)
    ?_ ?_ ?_
  · rintro i ⟨L, hL⟩
    refine ⟨L, ?_⟩
    rw [hL, RootPairing.reflection_reflectionPerm, reflection_mul_self, one_mul]
  · intro i hi
    exact ⟨[⟨i, hi⟩], by simp⟩
  · rintro i j ⟨L, hL⟩ hj
    refine ⟨⟨j, hj⟩ :: (L ++ [⟨j, hj⟩]), ?_⟩
    rw [word_cons, word_concat, hL, RootPairing.reflection_reflectionPerm, mul_assoc]

/-- Every element of the reflection group is a product of simple reflections. -/
theorem exists_word_eq {w : M ≃ₗ[ℤ] M} (hw : w ∈ reflectionGroup P) :
    ∃ L : List b.support, word b L = w := by
  induction hw using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact exists_word_eq_reflection b i
  | one => exact ⟨[], rfl⟩
  | mul u v _ _ hu hv =>
    obtain ⟨L, rfl⟩ := hu
    obtain ⟨L', rfl⟩ := hv
    exact ⟨L ++ L', word_append b L L'⟩
  | inv u _ hu =>
    obtain ⟨L, rfl⟩ := hu
    exact ⟨L.reverse, word_reverse b L⟩

/-- **Deletion lemma.** If a word sends the simple root `α_a` to a negative root, then the
word followed by `s_a` is a word with one letter less. -/
theorem exists_word_delete (L : List b.support) (a : b.support)
    (h : -(word b L (P.root a)) ∈ positiveCone P b) :
    ∃ L' : List b.support, L'.length + 1 = L.length ∧ word b L' = word b L * P.reflection a := by
  induction L with
  | nil => exact absurd h (neg_root_notMem_of_mem b (root_mem_positiveCone P b a))
  | cons c L ih =>
    by_cases h0 : -(word b L (P.root a)) ∈ positiveCone P b
    · obtain ⟨L', hlen, hL'⟩ := ih h0
      exact ⟨c :: L', by simp [hlen], by rw [word_cons, word_cons, hL', mul_assoc]⟩
    · obtain ⟨σ, hσ⟩ := exists_perm_of_mem_reflectionGroup (word_mem b L)
      have hroot : word b L (P.root a) = P.root (σ a) := (hσ a).1
      rw [hroot, neg_root_mem_iff, not_not] at h0
      have hc : σ a = c := by
        by_contra hne
        have h1 := reflection_root_mem_of_ne b c.2 h0 hne
        rw [word_cons] at h
        change -(P.reflection c (word b L (P.root a))) ∈ positiveCone P b at h
        rw [hroot] at h
        rw [← RootPairing.root_reflectionPerm] at h h1
        exact neg_root_notMem_of_mem b h1 h
      refine ⟨L, by simp, ?_⟩
      have hconj := mul_reflection_mul_inv (word_mem b L) (hroot.trans (congrArg P.root hc))
      rw [word_cons, ← hconj]
      simp [mul_assoc]

/-- An element of the reflection group sending every simple root to a positive root is the
identity. -/
theorem word_eq_one_of_forall (L : List b.support)
    (h : ∀ a : b.support, word b L (P.root a) ∈ positiveCone P b) : word b L = 1 := by
  suffices H : ∀ n, ∀ L : List b.support, L.length = n →
      (∀ a : b.support, word b L (P.root a) ∈ positiveCone P b) → word b L = 1 from
    H _ L rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hn h
    rcases L.eq_nil_or_concat' with rfl | ⟨L1, a, rfl⟩
    · rfl
    · have h1 : -(word b L1 (P.root a)) ∈ positiveCone P b := by
        have := h a
        rw [word_concat] at this
        change word b L1 (P.reflection a (P.root a)) ∈ positiveCone P b at this
        rwa [RootPairing.reflection_apply_self, map_neg] at this
      obtain ⟨L', hlen, hL'⟩ := exists_word_delete b L1 a h1
      rw [← word_concat] at hL'
      rw [← hL'] at h ⊢
      simp only [List.length_append, List.length_singleton] at hn
      exact ih L'.length (by omega) L' rfl h

theorem eq_one_of_forall_simple {w : M ≃ₗ[ℤ] M} (hw : w ∈ reflectionGroup P)
    (h : ∀ a : b.support, w (P.root a) ∈ positiveCone P b) : w = 1 := by
  obtain ⟨L, rfl⟩ := exists_word_eq b hw
  exact word_eq_one_of_forall b L h

/-! ### Strictly dominant elements have trivial stabilizer -/

omit [Finite ι] [P.IsReduced] in
theorem rootForm_root_mul_pairing [Fintype ι] (j : ι) (x : M) :
    P.RootForm (P.root j) (P.root j) * P.toLinearMap x (P.coroot j) =
      2 * P.RootForm (P.root j) x := by
  have h := congrArg (fun n => P.toLinearMap x n) (P.rootForm_self_smul_coroot j)
  simp only [map_smul, map_nsmul, smul_eq_mul, nsmul_eq_mul] at h
  rw [P.toLinearMap_apply_apply_Polarization] at h
  push_cast at h
  exact h

omit [Finite ι] [P.IsReduced] in
theorem rootForm_root_self_pos [Fintype ι] (j : ι) : 0 < P.RootForm (P.root j) (P.root j) := by
  rw [P.rootForm_root_self]
  refine Finset.sum_pos' (fun i _ => mul_self_nonneg _) ⟨j, Finset.mem_univ _, ?_⟩
  rw [P.pairing_same]
  norm_num

/-- An element is strictly dominant when its pairing with every simple coroot is positive. -/
def IsStrictlyDominant (x : M) : Prop :=
  ∀ a : b.support, 0 < P.toLinearMap x (P.coroot a)

omit [Finite ι] [P.IsReduced] in
theorem IsStrictlyDominant.isDominant {x : M} (hx : IsStrictlyDominant b x) :
    IsDominant P b x := fun a => (hx a).le

/-- An element of the reflection group carrying a strictly dominant element to a dominant
element is the identity. -/
theorem eq_one_of_isDominant_apply {w : M ≃ₗ[ℤ] M} (hw : w ∈ reflectionGroup P) {x : M}
    (hx : IsStrictlyDominant b x) (hwx : IsDominant P b (w x)) : w = 1 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  refine eq_one_of_forall_simple b hw fun a => ?_
  obtain ⟨σ, hσ⟩ := exists_perm_of_mem_reflectionGroup hw
  rw [(hσ a).1]
  by_contra hneg
  have hneg' := (neg_root_mem_iff b (σ a)).mpr hneg
  have h1 : 0 < P.toLinearMap (w x) (P.coroot (σ a)) := by
    change 0 < P.coroot' (σ a) (w x)
    rw [(hσ a).2 x]
    exact hx a
  have h2 := rootForm_nonneg_of_mem_positiveCone hwx hneg'
  have h3 := rootForm_root_mul_pairing (P := P) (σ a) (w x)
  have h4 := rootForm_root_self_pos (P := P) (σ a)
  rw [map_neg, LinearMap.neg_apply] at h2
  nlinarith

/-! ### Determinants of reflections -/

omit [Finite ι] [P.IsReduced] in
theorem det_reflection [Module.Free ℤ M] [Module.Finite ℤ M] (i : ι) :
    LinearMap.det (P.reflection i).toLinearMap = -1 := by
  classical
  let B := Module.Free.chooseBasis ℤ M
  have hlin : (P.reflection i).toLinearMap =
      LinearMap.id - (P.coroot' i).smulRight (P.root i) := by
    ext x
    simp [RootPairing.reflection_apply]
  have hdot : (P.coroot' i ∘ B) ⬝ᵥ (B.repr (P.root i)) = 2 := by
    have h2 : P.coroot' i (P.root i) = 2 := by simp
    conv_rhs => rw [← h2, ← B.sum_repr (P.root i)]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, Function.comp_apply, mul_comm]
  rw [hlin, ← LinearMap.det_toMatrix B, map_sub, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit, Matrix.det_one_sub_mul_comm,
    Matrix.det_unique, Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.replicateRow_mul_replicateCol_apply, hdot]
  norm_num

omit [Finite ι] [P.IsReduced] in
theorem det_mul (v w : M ≃ₗ[ℤ] M) :
    LinearMap.det (v * w).toLinearMap = LinearMap.det v.toLinearMap * LinearMap.det w.toLinearMap := by
  rw [← LinearEquiv.coe_det, ← LinearEquiv.coe_det, ← LinearEquiv.coe_det, map_mul, Units.val_mul]

omit [Finite ι] [P.IsReduced] in
theorem det_word [Module.Free ℤ M] [Module.Finite ℤ M] (L : List b.support) :
    LinearMap.det (word b L).toLinearMap = (-1) ^ L.length := by
  induction L with
  | nil => simp
  | cons a L ih => rw [word_cons, det_mul, det_reflection, ih, List.length_cons, pow_succ']

/-! ### The half sum of positive roots -/

/-- The half sum `ρ` of the positive roots pairs to `1` with every simple coroot. -/
theorem pairing_rho_eq_one {ρ : M}
    (hρ : 2 • ρ = ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), P.root i) (a : b.support) :
    P.toLinearMap ρ (P.coroot a) = 1 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let π := P.reflectionPerm a
  let h : ι → ℤ := fun i =>
    if P.root i ∈ positiveCone P b then P.toLinearMap (P.root i) (P.coroot a) else 0
  have hρ' : P.toLinearMap (2 • ρ) (P.coroot a) = ∑ i, h i := by
    rw [hρ]
    simp_rw [finsum_eq_if]
    rw [finsum_eq_sum_of_fintype, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [h]
    split_ifs <;> simp
  have hπ : ∀ i, P.toLinearMap (P.root (π i)) (P.coroot a) =
      -P.toLinearMap (P.root i) (P.coroot a) := by
    intro i
    simp only [π, RootPairing.root_reflectionPerm, RootPairing.reflection_apply, map_sub,
      map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    change P.toLinearMap (P.root i) (P.coroot a) -
      P.coroot' a (P.root i) * P.toLinearMap (P.root a) (P.coroot a) = _
    rw [RootPairing.root_coroot_two]
    change P.coroot' a (P.root i) - P.coroot' a (P.root i) * 2 = -P.coroot' a (P.root i)
    ring
  have hne : (a : ι) ≠ π a := P.ne_neg (i := (a : ι))
  have hpt : ∀ i, h (π i) + h i =
      (if i = a then 2 else 0) + (if i = π a then 2 else 0) := by
    intro i
    by_cases hia : i = a
    · subst hia
      have h1 : h (π a) = 0 := ite_eq_right (root_reflectionPerm_self_notMem b a.2)
      have h2 : h a = 2 := by
        simp only [h, ite_eq_left (root_mem_positiveCone P b a), RootPairing.root_coroot_two]
      rw [h1, h2, ite_eq_left rfl, ite_eq_right hne]
      norm_num
    by_cases hia' : i = π a
    · subst hia'
      have h1 : h (π (π a)) = 2 := by
        simp only [h, π, RootPairing.reflectionPerm_self, ite_eq_left (root_mem_positiveCone P b a),
          RootPairing.root_coroot_two]
      have h2 : h (π a) = 0 := ite_eq_right (root_reflectionPerm_self_notMem b a.2)
      rw [h1, h2, ite_eq_right (Ne.symm hne), ite_eq_left rfl]
      norm_num
    · have hiff : P.root (π i) ∈ positiveCone P b ↔ P.root i ∈ positiveCone P b :=
        root_reflectionPerm_mem_iff b a.2 hia hia'
      simp only [h, hπ, hiff, ite_eq_right hia, ite_eq_right hia']
      split_ifs <;> ring
  have hsum : ∑ i, (h (π i) + h i) = 4 := by
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _)]
    norm_num
  rw [Finset.sum_add_distrib, Equiv.sum_comp π h, ← hρ'] at hsum
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

end Langlands.LinearAlgebra.WeylCharacter
