import Langlands.Representation.Archimedean.LowerVermaPBW

/-! # Poincaré–Birkhoff–Witt coordinates for the two-block grading -/

noncomputable section

open scoped Classical
set_option autoImplicit false

namespace Langlands.Archimedean.TwoBlockEnveloping

open VermaPBW Kostant
open Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n a : ℕ)

local notation "U" => VermaGL.glU n

/-- The block grading element has entry one on the first block and zero
on the second. -/
def blockDiagonalGrade (i : Fin n) : ℂ := if i.val < a then 1 else 0

/-- The adjoint weight of one matrix-unit generator for the block grading. -/
def blockLetterWeight (c : Idx n) : ℂ :=
  blockDiagonalGrade n a c.1 - blockDiagonalGrade n a c.2

theorem blockLetterWeight_cases (c : Idx n) :
    blockLetterWeight n a c = 1 ∨ blockLetterWeight n a c = 0 ∨
      blockLetterWeight n a c = -1 := by
  unfold blockLetterWeight blockDiagonalGrade
  split_ifs <;> norm_num

private def lettersOfWeight (k : ℂ) : List {c : Idx n // blockLetterWeight n a c = k} :=
  Finset.univ.toList

/-- Enumeration of the matrix-unit indices of a fixed block weight. -/
def weightLetters (k : ℂ) : List (Idx n) :=
  (lettersOfWeight n a k).map Subtype.val

theorem mem_weightLetters (k : ℂ) (c : Idx n) :
    c ∈ weightLetters n a k ↔ blockLetterWeight n a c = k := by
  constructor
  · intro hc
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
    exact d.property
  · intro hc
    exact List.mem_map.mpr ⟨⟨c, hc⟩, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

private theorem weightLetters_nodup (k : ℂ) : (weightLetters n a k).Nodup :=
  (Finset.nodup_toList _).map Subtype.val_injective

/-- The PBW order puts upper radical letters first, then Levi letters and
then lower radical letters. -/
def blockLetters : List (Idx n) :=
  weightLetters n a 1 ++ (weightLetters n a 0 ++ weightLetters n a (-1))

private theorem blockLetters_nodup : (blockLetters n a).Nodup := by
  unfold blockLetters
  refine List.nodup_append.mpr ⟨weightLetters_nodup n a _, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨weightLetters_nodup n a _, weightLetters_nodup n a _, ?_⟩
    intro x hx y hy e
    subst y
    have he := ((mem_weightLetters n a _ x).mp hx).symm.trans ((mem_weightLetters n a _ x).mp hy)
    norm_num at he
  · intro x hx y hy e
    subst y
    have h1 := (mem_weightLetters n a _ x).mp hx
    rcases List.mem_append.mp hy with hy | hy
    · have he := h1.symm.trans ((mem_weightLetters n a _ x).mp hy)
      norm_num at he
    · have he := h1.symm.trans ((mem_weightLetters n a _ x).mp hy)
      norm_num at he

private theorem mem_blockLetters (c : Idx n) : c ∈ blockLetters n a := by
  unfold blockLetters
  simp only [List.mem_append, mem_weightLetters]
  exact blockLetterWeight_cases n a c

/-- The Poincaré–Birkhoff–Witt basis in the two-block order. -/
def blockPBWBasis : Module.Basis (Idx n →₀ ℕ) ℂ U :=
  pbwBasis (stdB n) (AssocSymbol.symbolData (stdB n)) (AssocSymbol.symbolData_ξ_basis _)
    (blockLetters_nodup n a) (mem_blockLetters n a)

theorem blockPBWBasis_apply (α : Idx n →₀ ℕ) :
    blockPBWBasis n a α = W n (expand (blockLetters n a) α) := by
  rw [blockPBWBasis, pbwBasis_apply]
  rfl

/-- The element of the enveloping algebra defining the block grading. -/
def blockGradeElement : U :=
  UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal (blockDiagonalGrade n a))

/-- The weight of a complete ordered word is the sum of its letter weights. -/
def blockMonomialWeight (α : Idx n →₀ ℕ) : ℂ :=
  ((expand (blockLetters n a) α).map (blockLetterWeight n a)).sum

private theorem grade_mul_word (l : List (Idx n)) :
    blockGradeElement n a * W n l =
      W n l * blockGradeElement n a + (l.map (blockLetterWeight n a)).sum • W n l := by
  induction l with
  | nil => simp only [W_nil, mul_one, one_mul, List.map_nil, List.sum_nil, zero_smul, add_zero]
  | cons c l ih =>
    rw [W_cons, List.map_cons, List.sum_cons, ← mul_assoc,
      show blockGradeElement n a * UniversalEnvelopingAlgebra.ι ℂ (unitE n c) =
          UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * blockGradeElement n a +
            blockLetterWeight n a c • UniversalEnvelopingAlgebra.ι ℂ (unitE n c)
        from ι_diagonal_mul n (blockDiagonalGrade n a) c,
      add_mul, smul_mul_assoc, mul_assoc, ih, mul_add, mul_smul_comm, add_smul]
    simp only [mul_assoc]
    abel

theorem blockGrade_commutator_basis (α : Idx n →₀ ℕ) :
    blockGradeElement n a * blockPBWBasis n a α - blockPBWBasis n a α * blockGradeElement n a =
      blockMonomialWeight n a α • blockPBWBasis n a α := by
  rw [blockPBWBasis_apply, grade_mul_word, add_sub_cancel_left, blockMonomialWeight]

/-- Every nonzero PBW coefficient of an element commuting with the grading
element has weight zero. -/
theorem blockMonomialWeight_eq_zero_of_commute (z : U)
    (hz : Commute (blockGradeElement n a) z) (α : Idx n →₀ ℕ)
    (hα : (blockPBWBasis n a).repr z α ≠ 0) :
    blockMonomialWeight n a α = 0 := by
  let B := blockPBWBasis n a
  let H := blockGradeElement n a
  have h : B.coord α ∘ₗ (LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H) =
      blockMonomialWeight n a α • B.coord α := by
    refine B.ext fun β => ?_
    change B.coord α (blockGradeElement n a * blockPBWBasis n a β -
      blockPBWBasis n a β * blockGradeElement n a) =
      blockMonomialWeight n a α • B.coord α (blockPBWBasis n a β)
    rw [blockGrade_commutator_basis, map_smul]
    by_cases hβ : β = α
    · subst β; rfl
    · simp [B, Module.Basis.coord_apply, Module.Basis.repr_self, hβ]
  have he := LinearMap.congr_fun h z
  change B.coord α (H * z - z * H) =
    blockMonomialWeight n a α * B.coord α z at he
  rw [hz.eq, sub_self, map_zero, Module.Basis.coord_apply] at he
  exact (mul_eq_zero.mp he.symm).resolve_right hα

private theorem sum_wordWeight_of_weightLetters (α : Idx n →₀ ℕ) (k : ℂ) :
    ((expand (weightLetters n a k) α).map (blockLetterWeight n a)).sum =
      ((expand (weightLetters n a k) α).length : ℂ) * k := by
  have key (l : List (Idx n)) (hl : ∀ c ∈ l, blockLetterWeight n a c = k) :
      (l.map (blockLetterWeight n a)).sum = (l.length : ℂ) * k := by
    induction l with
    | nil => simp
    | cons c l ih =>
      rw [List.map_cons, List.sum_cons, hl c List.mem_cons_self,
        ih (fun d hd => hl d (List.mem_cons_of_mem _ hd)), List.length_cons, Nat.cast_succ, add_mul,
        one_mul, add_comm]
  exact key _ fun c hc => (mem_weightLetters n a k c).mp (mem_expand hc)

/-- Weight zero equates the lengths of the two radical parts of the ordered monomial. -/
theorem upper_length_eq_lower_of_weight_zero (α : Idx n →₀ ℕ)
    (hα : blockMonomialWeight n a α = 0) :
    (expand (weightLetters n a 1) α).length = (expand (weightLetters n a (-1)) α).length := by
  rw [blockMonomialWeight, blockLetters, expand_append, expand_append, List.map_append,
    List.map_append, List.sum_append, List.sum_append,
    sum_wordWeight_of_weightLetters, sum_wordWeight_of_weightLetters, sum_wordWeight_of_weightLetters,
    mul_one, mul_zero, mul_neg, mul_one, zero_add, ← sub_eq_add_neg, sub_eq_zero] at hα
  exact_mod_cast hα

private theorem levi_relation_trans (i j k : Fin n) :
    blockLetterWeight n a (i, j) = 0 → blockLetterWeight n a (j, k) = 0 →
      blockLetterWeight n a (i, k) = 0 := by
  simp only [blockLetterWeight, sub_eq_zero]
  exact Eq.trans

/-- The Lie algebra of matrices supported within the two diagonal blocks. -/
def blockLevi : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  subalg n (fun i j => blockLetterWeight n a (i, j) = 0) (levi_relation_trans n a)

/-- The block diagonal inclusion on the actual universal enveloping algebra. -/
def leviInclusion : UniversalEnvelopingAlgebra ℂ (blockLevi n a) →ₐ[ℂ] U :=
  subInc n (fun i j => blockLetterWeight n a (i, j) = 0) (levi_relation_trans n a)

/-- The span of enveloping elements with an upper-radical matrix unit at the left. -/
def upperRadicalRightSpan : Submodule ℂ U :=
  Submodule.span ℂ (Set.range fun p : {c : Idx n // blockLetterWeight n a c = 1} × U =>
    UniversalEnvelopingAlgebra.ι ℂ (unitE n p.1.val) * p.2)

private theorem basis_mem_levi_sup_upperRadicalRightSpan (α : Idx n →₀ ℕ)
    (hα : blockMonomialWeight n a α = 0) :
    blockPBWBasis n a α ∈ (leviInclusion n a).range.toSubmodule ⊔ upperRadicalRightSpan n a := by
  rw [blockPBWBasis_apply, blockLetters, expand_append, expand_append]
  cases hU : expand (weightLetters n a 1) α with
  | nil =>
    have hL := upper_length_eq_lower_of_weight_zero n a α hα
    rw [hU, List.length_nil, eq_comm, List.length_eq_zero_iff] at hL
    simp only [hL, List.nil_append, List.append_nil]
    apply Submodule.mem_sup_left
    let l := expand (lettersOfWeight n a 0) (α.subtypeDomain fun c => blockLetterWeight n a c = 0)
    refine ⟨word ℂ (blockLevi n a)
      (l.map (subBasis n _ (levi_relation_trans n a))), ?_⟩
    change subInc n _ (levi_relation_trans n a) _ = _
    unfold blockLevi
    rw [subInc_word, weightLetters, expand_map _ _ _ _ (fun c _ => Finsupp.subtypeDomain_apply.symm)]
  | cons c l =>
    apply Submodule.mem_sup_right
    have hc' : c ∈ expand (weightLetters n a 1) α := by
      rw [hU]
      exact List.mem_cons_self
    have hc : blockLetterWeight n a c = 1 :=
      (mem_weightLetters n a 1 c).mp (mem_expand hc')
    rw [List.cons_append, W_cons]
    exact Submodule.subset_span ⟨(⟨c, hc⟩, _), rfl⟩

/-- An element commuting with the block grading is a sum of an enveloping
element of the Levi and an element of the upper radical span. -/
theorem mem_levi_sup_upperRadicalRightSpan_of_commute (z : U)
    (hz : Commute (blockGradeElement n a) z) :
    z ∈ (leviInclusion n a).range.toSubmodule ⊔ upperRadicalRightSpan n a := by
  rw [← (blockPBWBasis n a).linearCombination_repr z,
    Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
  exact basis_mem_levi_sup_upperRadicalRightSpan n a α
    (blockMonomialWeight_eq_zero_of_commute n a z hz α (Finsupp.mem_support_iff.mp hα))

end Langlands.Archimedean.TwoBlockEnveloping
