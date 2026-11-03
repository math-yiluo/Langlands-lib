import Langlands.Group.RootPairingCoxeterProof

/-! # Positive roots, simple sign changes and root-sign Coxeter uniqueness -/

noncomputable section

namespace Langlands.Group.RootPairingSigns

open Set Function IsAddIndecomposable

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] (f : Module.Dual R M)

omit [P.IsCrystallographic] in
private lemma root_mem_closure {i : ι} (hi : 0 < f (P.root i)) :
    P.root i ∈ AddSubmonoid.closure (P.root '' baseOf P.root (f : M →+ R)) := by
  rw [AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
  exact AddSubmonoid.subset_closure ⟨i, hi, rfl⟩

omit [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
private lemma pos_of_mem_base {a : ι} (ha : a ∈ baseOf P.root (f : M →+ R)) :
    0 < f (P.root a) :=
  baseOf_subset_pos P.root (f : M →+ R) ha

/-- If two elements of the monoid spanned by the simple roots add up to a multiple of a simple
root `α`, then each of them is a natural multiple of `α`. -/
lemma eq_nsmul_of_add_eq_smul (hf : ∀ i, f (P.root i) ≠ 0) {x y : M}
    (hx : x ∈ AddSubmonoid.closure (P.root '' baseOf P.root (f : M →+ R)))
    (hy : y ∈ AddSubmonoid.closure (P.root '' baseOf P.root (f : M →+ R)))
    {a : ι} (ha : a ∈ baseOf P.root (f : M →+ R)) {t : R} (hxy : x + y = t • P.root a) :
    ∃ n : ℕ, x = n • P.root a := by
  classical
  set Δ := baseOf P.root (f : M →+ R) with hΔ
  have : Fintype Δ := Fintype.ofFinite _
  have himg : P.root '' Δ = range (fun b : Δ => P.root b) := image_eq_range _ _
  rw [himg] at hx hy
  obtain ⟨cx, rfl⟩ := AddSubmonoid.exists_of_mem_closure_range _ x hx
  obtain ⟨cy, rfl⟩ := AddSubmonoid.exists_of_mem_closure_range _ y hy
  have hli : LinearIndependent R (fun b : Δ => P.root b) := P.linearIndepOn_root_baseOf' f hf
  let a' : Δ := ⟨a, ha⟩
  let g : Δ → R := fun b => ((cx b : R) + cy b) - if b = a' then t else 0
  have hg : ∑ b, g b • P.root (b : ι) = 0 := by
    have : ∑ b, g b • P.root (b : ι) =
        (∑ b, cx b • P.root (b : ι)) + (∑ b, cy b • P.root (b : ι)) - t • P.root a := by
      simp [g, sub_smul, add_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_smul,
        Nat.cast_smul_eq_nsmul, a']
    rw [this, hxy, sub_self]
  have hg0 := Fintype.linearIndependent_iff.mp hli g hg
  refine ⟨cx a', ?_⟩
  rw [Finset.sum_eq_single a']
  · intro b _ hb
    have h0 := hg0 b
    simp only [g, hb, ↓reduceIte, sub_zero] at h0
    have h1 : (0 : R) ≤ cx b := Nat.cast_nonneg _
    have h2 : (0 : R) ≤ cy b := Nat.cast_nonneg _
    have hcx : (cx b : R) = 0 := by linarith
    have : cx b = 0 := by exact_mod_cast hcx
    simp [this]
  · simp

/-- If a positive root becomes negative under the reflection in a simple root `α`, then it is a
natural multiple of `α`. -/
lemma eq_nsmul_of_reflection_neg (hf : ∀ i, f (P.root i) ≠ 0) {a i : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) (hi : 0 < f (P.root i))
    (hneg : f (P.reflection a (P.root i)) < 0) : ∃ n : ℕ, P.root i = n • P.root a := by
  obtain ⟨j, hj⟩ := P.neg_root_mem (P.reflectionPerm a i)
  rw [P.root_reflectionPerm] at hj
  have hjpos : 0 < f (P.root j) := by rw [hj, map_neg]; linarith
  refine eq_nsmul_of_add_eq_smul P f hf (root_mem_closure P f hi) (root_mem_closure P f hjpos) ha
    (t := P.pairing i a) ?_
  rw [hj, P.reflection_apply_root]
  abel

/-- A root is indivisible if it is not a multiple `n • β`, `n ≥ 2`, of a root `β`. -/
def Indivisible (i : ι) : Prop := ∀ n : ℕ, 2 ≤ n → ∀ j, n • P.root j ≠ P.root i

/-- Simple roots are indivisible. -/
lemma indivisible_of_mem_base (hf : ∀ i, f (P.root i) ≠ 0) {a : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) : Indivisible P a := by
  intro n hn j hj
  have ha0 := pos_of_mem_base P f ha
  have hjpos : 0 < f (P.root j) := by
    rw [← hj, map_nsmul, nsmul_eq_mul] at ha0
    exact pos_of_mul_pos_right ha0 (Nat.cast_nonneg n)
  have hy : (n - 1) • P.root j ∈ AddSubmonoid.closure (P.root '' baseOf P.root (f : M →+ R)) :=
    AddSubmonoid.nsmul_mem _ (root_mem_closure P f hjpos) _
  obtain ⟨m, hm⟩ := eq_nsmul_of_add_eq_smul P f hf (root_mem_closure P f hjpos) hy ha (t := 1)
    (by rw [one_smul, ← hj, ← succ_nsmul', Nat.sub_add_cancel (by omega)])
  rw [hm, smul_smul] at hj
  have h1 : ((n * m : ℕ) : R) • P.root a = (1 : R) • P.root a := by
    rw [Nat.cast_smul_eq_nsmul, hj, one_smul]
  have h2 : ((n * m : ℕ) : R) = 1 := smul_left_injective R (P.ne_zero a) h1
  have h3 : n * m = 1 := by exact_mod_cast h2
  have : n = 1 := Nat.eq_one_of_mul_eq_one_right h3
  omega

omit [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
private lemma indiv_reflectionPerm {a i : ι} (h : Indivisible P i) : Indivisible P (P.reflectionPerm a i) := by
  intro n hn j hj
  apply h n hn (P.reflectionPerm a j)
  rw [P.root_reflectionPerm, ← map_nsmul, hj, P.root_reflectionPerm, P.reflection_same]

omit [Finite ι] [P.IsCrystallographic] in
lemma eq_of_indivisible_of_eq_nsmul {a i : ι} (h : Indivisible P i) {n : ℕ}
    (hn : P.root i = n • P.root a) : i = a := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · exact absurd (by simpa using hn) (P.ne_zero i)
    · exact P.root.injective (by simpa using hn)
  · exact absurd hn.symm (h n h2 a)


omit [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
/-- Weyl transport preserves indivisibility, including in a nonreduced system. -/
theorem indivisible_weyl_image {i : ι} (hi : Indivisible P i) (w : P.weylGroup) :
    Indivisible P (P.weylGroupToPerm w i) := by
  intro n hn j hj
  apply hi n hn (P.weylGroupToPerm w⁻¹ j)
  have hback := congrArg (fun x : M => w⁻¹ • x) hj
  have hcomm : w⁻¹ • (n • P.root j) = n • (w⁻¹ • P.root j) :=
    map_nsmul (P.weylGroupRootRep w⁻¹) _ _
  rw [hcomm, ← P.weylGroup_apply_root w i, inv_smul_smul] at hback
  rwa [P.weylGroup_apply_root] at hback

/-- A positive Weyl image of a simple root sent negative by another simple
reflection is that second simple root. -/
theorem image_eq_simple_of_reflection_neg (hf : ∀ i, f (P.root i) ≠ 0)
    {a b : ι} (ha : a ∈ baseOf P.root (f : M →+ R))
    (hb : b ∈ baseOf P.root (f : M →+ R)) (w : P.weylGroup)
    (hpos : 0 < f (w • P.root a))
    (hneg : f (P.reflection b (w • P.root a)) < 0) :
    w • P.root a = P.root b := by
  have hi := indivisible_weyl_image P (indivisible_of_mem_base P f hf ha) w
  rw [P.weylGroup_apply_root] at hpos hneg ⊢
  obtain ⟨n, hn⟩ := eq_nsmul_of_reflection_neg P f hf hb hpos hneg
  rw [eq_of_indivisible_of_eq_nsmul P hi hn]

/-- Positive conjugacy of simple reflections detects equality of the actual
root labels without a reducedness hypothesis. -/
theorem root_eq_of_conj_simple (hf : ∀ i, f (P.root i) ≠ 0)
    (w : P.weylGroup) {a b : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R))
    (hb : b ∈ baseOf P.root (f : M →+ R))
    (hpos : 0 < f (w • P.root a))
    (heq : w * RootPairing.weylGroup.ofIdx P a * w⁻¹ =
      RootPairing.weylGroup.ofIdx P b) :
    w • P.root a = P.root b := by
  apply image_eq_simple_of_reflection_neg P f hf ha hb w hpos
  have hneg : P.reflection b (w • P.root a) = -(w • P.root a) := by
    change RootPairing.weylGroup.ofIdx P b • (w • P.root a) = _
    rw [← heq, mul_smul, mul_smul, inv_smul_smul]
    change w • P.reflection a (P.root a) = _
    rw [P.reflection_apply_self, smul_neg]
  rw [hneg, map_neg]
  exact neg_neg_of_pos hpos

end Langlands.Group.RootPairingSigns
