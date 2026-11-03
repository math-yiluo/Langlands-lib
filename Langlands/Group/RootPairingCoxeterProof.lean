import Langlands.Group.RootPairingCoxeterStatement
import Langlands.Group.CoxeterOfExchange
import Langlands.Group.RootPairingWeylGeneration
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Data.Set.Finite.List

/-!
# The Weyl group of a finite crystallographic root pairing is a Coxeter group

We prove `Langlands.Group.RootPairingWeylCoxeterStatement`.
-/

universe u₁ u₂ u₃ u₄

namespace Langlands.Group

open Set Function IsAddIndecomposable

section Weyl

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)

private lemma weyl_ext {g h : P.weylGroup} (H : ∀ m : M, g • m = h • m) : g = h := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  ext m
  exact H m

private lemma ofIdx_smul' (i : ι) (m : M) :
    RootPairing.weylGroup.ofIdx P i • m = P.reflection i m :=
  rfl

private lemma ofIdx_mul_self (i : ι) :
    RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P i = 1 :=
  weyl_ext P fun m => by rw [mul_smul, ofIdx_smul', ofIdx_smul', one_smul, P.reflection_same]

/-- Conjugating the reflection in a root by an element of the Weyl group gives the reflection in
the image root. -/
private lemma conj_ofIdx (u : P.weylGroup) (i : ι) :
    u * RootPairing.weylGroup.ofIdx P i * u⁻¹ =
      RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm u i) := by
  refine weyl_ext P fun m => ?_
  rw [mul_smul, mul_smul, ofIdx_smul', ofIdx_smul']
  have h1 : u • P.reflection i (u⁻¹ • m) =
      P.reflection ((u : RootPairing.Aut P).indexEquiv i) (u • u⁻¹ • m) :=
    RootPairing.Equiv.weightEquiv_reflection (u : RootPairing.Aut P) i (u⁻¹ • m)
  rw [h1, smul_inv_smul]
  rfl

end Weyl

section Ordered

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] (f : Module.Dual R M)

omit [P.IsCrystallographic] in
/-- Proportional roots give the same reflection. -/
private lemma ofIdx_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    RootPairing.weylGroup.ofIdx P j = RootPairing.weylGroup.ofIdx P i := by
  have : IsAddTorsionFree N := .of_isTorsionFree R N
  have hc := RootPairing.smul_coroot_eq_of_root_eq_smul i j t h
  refine weyl_ext P fun m => ?_
  rw [ofIdx_smul', ofIdx_smul', P.reflection_apply, P.reflection_apply, h]
  have hc' : P.coroot' i m = t * P.coroot' j m := by simp [RootPairing.coroot', ← hc]
  rw [hc', smul_smul, mul_comm t]

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
private lemma eq_nsmul_of_add_eq_smul (hf : ∀ i, f (P.root i) ≠ 0) {x y : M}
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
private lemma eq_nsmul_of_reflection_neg (hf : ∀ i, f (P.root i) ≠ 0) {a i : ι}
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
private def Indiv (i : ι) : Prop := ∀ n : ℕ, 2 ≤ n → ∀ j, n • P.root j ≠ P.root i

/-- Simple roots are indivisible. -/
private lemma indiv_of_mem_base (hf : ∀ i, f (P.root i) ≠ 0) {a : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) : Indiv P a := by
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
private lemma indiv_reflectionPerm {a i : ι} (h : Indiv P i) : Indiv P (P.reflectionPerm a i) := by
  intro n hn j hj
  apply h n hn (P.reflectionPerm a j)
  rw [P.root_reflectionPerm, ← map_nsmul, hj, P.root_reflectionPerm, P.reflection_same]

omit [Finite ι] [P.IsCrystallographic] in
private lemma eq_of_indiv_of_eq_nsmul {a i : ι} (h : Indiv P i) {n : ℕ}
    (hn : P.root i = n • P.root a) : i = a := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · exact absurd (by simpa using hn) (P.ne_zero i)
    · exact P.root.injective (by simpa using hn)
  · exact absurd hn.symm (h n h2 a)

/-- The reflections in distinct simple roots are distinct. -/
private lemma ofIdx_injOn_base (hf : ∀ i, f (P.root i) ≠ 0) {a b : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) (hb : b ∈ baseOf P.root (f : M →+ R))
    (h : RootPairing.weylGroup.ofIdx P a = RootPairing.weylGroup.ofIdx P b) : a = b := by
  have h1 : RootPairing.weylGroup.ofIdx P a • P.root a =
      RootPairing.weylGroup.ofIdx P b • P.root a := by rw [h]
  rw [ofIdx_smul', ofIdx_smul', P.reflection_apply_self, P.reflection_apply_root] at h1
  have hca := root_mem_closure P f (pos_of_mem_base P f ha)
  obtain ⟨n, hn⟩ := eq_nsmul_of_add_eq_smul P f hf hca hca hb (t := P.pairing a b)
    (by rw [eq_sub_iff_add_eq, neg_add_eq_iff_eq_add] at h1; exact h1.symm)
  exact eq_of_indiv_of_eq_nsmul P (indiv_of_mem_base P f hf ha) hn

/-- The inversion set of `w`: the indivisible positive roots made negative by `w`. -/
private def invSet (w : P.weylGroup) : Set ι :=
  {i | 0 < f (P.root i) ∧ (∀ n : ℕ, 2 ≤ n → ∀ j, n • P.root j ≠ P.root i) ∧
    f (w • P.root i) < 0}

omit [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
private lemma smul_root_ne_zero (hf : ∀ i, f (P.root i) ≠ 0) (w : P.weylGroup) (i : ι) :
    f (w • P.root i) ≠ 0 := by
  rw [RootPairing.weylGroup_apply_root]
  exact hf _

/-- The reflection in a simple root `α` permutes the indivisible positive roots other than `α`. -/
private lemma pos_reflectionPerm (hf : ∀ i, f (P.root i) ≠ 0) {a i : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) (hi : 0 < f (P.root i)) (hind : Indiv P i)
    (hne : i ≠ a) : 0 < f (P.root (P.reflectionPerm a i)) ∧ P.reflectionPerm a i ≠ a := by
  refine ⟨?_, fun heq => ?_⟩
  · by_contra hle
    have hlt : f (P.reflection a (P.root i)) < 0 := by
      rw [← P.root_reflectionPerm]
      exact lt_of_le_of_ne (not_lt.mp hle) (hf _)
    obtain ⟨n, hn⟩ := eq_nsmul_of_reflection_neg P f hf ha hi hlt
    exact hne (eq_of_indiv_of_eq_nsmul P hind hn)
  · have h1 := congrArg (P.reflectionPerm a) heq
    rw [P.reflectionPerm_self] at h1
    rw [h1, P.root_reflectionPerm, P.reflection_apply_self, map_neg] at hi
    linarith [pos_of_mem_base P f ha]

private lemma invSet_mul_sdiff (hf : ∀ i, f (P.root i) ≠ 0) (w : P.weylGroup) {a : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) :
    invSet P f (w * RootPairing.weylGroup.ofIdx P a) \ {a} =
      P.reflectionPerm a ⁻¹' (invSet P f w \ {a}) := by
  ext i
  have hsm : (w * RootPairing.weylGroup.ofIdx P a) • P.root i =
      w • P.root (P.reflectionPerm a i) := by
    rw [mul_smul, ofIdx_smul', P.root_reflectionPerm]
  simp only [invSet, mem_sdiff, mem_singleton_iff, mem_preimage, mem_ofPred_eq, hsm]
  constructor
  · rintro ⟨⟨hi, hind, hw⟩, hne⟩
    obtain ⟨h1, h2⟩ := pos_reflectionPerm P f hf ha hi hind hne
    exact ⟨⟨h1, indiv_reflectionPerm P hind, hw⟩, h2⟩
  · rintro ⟨⟨hi, hind, hw⟩, hne⟩
    obtain ⟨h1, h2⟩ := pos_reflectionPerm P f hf ha hi hind hne
    rw [P.reflectionPerm_self] at h1 h2
    have hind' := indiv_reflectionPerm P (a := a) hind
    rw [P.reflectionPerm_self] at hind'
    exact ⟨⟨h1, hind', hw⟩, h2⟩

private lemma ncard_invSet_mul (hf : ∀ i, f (P.root i) ≠ 0) (w : P.weylGroup) {a : ι}
    (ha : a ∈ baseOf P.root (f : M →+ R)) :
    (0 < f (w • P.root a) →
      (invSet P f (w * RootPairing.weylGroup.ofIdx P a)).ncard = (invSet P f w).ncard + 1) ∧
    (f (w • P.root a) < 0 →
      (invSet P f (w * RootPairing.weylGroup.ofIdx P a)).ncard + 1 = (invSet P f w).ncard) := by
  have hsd : (invSet P f (w * RootPairing.weylGroup.ofIdx P a) \ {a}).ncard =
      (invSet P f w \ {a}).ncard := by
    rw [invSet_mul_sdiff P f hf w ha]
    exact ncard_preimage_of_injective_subset_range (P.reflectionPerm a).injective
      (by simp)
  have hsm : (w * RootPairing.weylGroup.ofIdx P a) • P.root a = -(w • P.root a) := by
    rw [mul_smul, ofIdx_smul', P.reflection_apply_self, smul_neg]
  have hpa := pos_of_mem_base P f ha
  have hia := indiv_of_mem_base P f hf ha
  constructor
  · intro hpos
    have h1 : a ∈ invSet P f (w * RootPairing.weylGroup.ofIdx P a) :=
      ⟨hpa, hia, by rw [hsm, map_neg]; linarith⟩
    have h2 : a ∉ invSet P f w := fun h => by linarith [h.2.2]
    rw [← ncard_sdiff_singleton_add_one h1, hsd, sdiff_singleton_eq_self h2]
  · intro hneg
    have h1 : a ∉ invSet P f (w * RootPairing.weylGroup.ofIdx P a) := fun h => by
      have := h.2.2
      rw [hsm, map_neg] at this
      linarith
    have h2 : a ∈ invSet P f w := ⟨hpa, hia, hneg⟩
    rw [← ncard_sdiff_singleton_add_one h2, ← hsd, sdiff_singleton_eq_self h1]

/-- The reflection in the simple root `b`, indexed by the base. -/
private abbrev sr (b : baseOf P.root (f : M →+ R)) : P.weylGroup :=
  RootPairing.weylGroup.ofIdx P (b : ι)

/-- The exchange property for the inversion count. -/
private lemma exchange (hf : ∀ i, f (P.root i) ≠ 0) (x : List (baseOf P.root (f : M →+ R)))
    (b : baseOf P.root (f : M →+ R)) (hneg : f ((x.map (sr P f)).prod • P.root b) < 0) :
    ∃ k < x.length, (x.map (sr P f)).prod * sr P f b = ((x.eraseIdx k).map (sr P f)).prod := by
  induction x with
  | nil =>
    simp only [List.map_nil, List.prod_nil, one_smul] at hneg
    exact absurd hneg (not_lt.mpr (pos_of_mem_base P f b.2).le)
  | cons c x ih =>
    set u := (x.map (sr P f)).prod with hu
    have hprod : ((c :: x).map (sr P f)).prod = sr P f c * u := by simp [hu]
    rw [hprod] at hneg ⊢
    by_cases h : f (u • P.root b) < 0
    · obtain ⟨k, hk, he⟩ := ih h
      refine ⟨k + 1, by simpa using hk, ?_⟩
      rw [List.eraseIdx_cons_succ, List.map_cons, List.prod_cons, mul_assoc, he]
    · have hpos : 0 < f (u • P.root b) :=
        lt_of_le_of_ne (not_lt.mp h) (smul_root_ne_zero P f hf u b).symm
      rw [RootPairing.weylGroup_apply_root] at hpos
      rw [mul_smul, RootPairing.weylGroup_apply_root, ofIdx_smul'] at hneg
      obtain ⟨n, hn⟩ := eq_nsmul_of_reflection_neg P f hf c.2 hpos hneg
      have hc : RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm u b) = sr P f c := by
        rw [← Nat.cast_smul_eq_nsmul R] at hn
        exact ofIdx_eq_of_root_eq_smul P hn
      have hconj : u * sr P f b = sr P f c * u := by
        rw [← hc, ← conj_ofIdx P u b, inv_mul_cancel_right]
      refine ⟨0, by simp, ?_⟩
      rw [List.eraseIdx_cons_zero, mul_assoc, hconj, ← mul_assoc, ofIdx_mul_self, one_mul]

/-- The theorem, assuming that the simple reflections generate the Weyl group. -/
private theorem main_of_generates (hf : ∀ i, f (P.root i) ≠ 0)
    (hgen : ∀ w : P.weylGroup, ∃ x : List (baseOf P.root (f : M →+ R)),
      (x.map (sr P f)).prod = w) :
    Finite P.weylGroup ∧
    ∃ (Mx : CoxeterMatrix (IsAddIndecomposable.baseOf P.root (f : M →+ R)))
      (cs : CoxeterSystem Mx P.weylGroup),
      (∀ b, cs.simple b = RootPairing.weylGroup.ofIdx P b) ∧
      (∀ w, cs.length w = Set.ncard {i | 0 < f (P.root i) ∧
          (∀ n : ℕ, 2 ≤ n → ∀ j, n • P.root j ≠ P.root i) ∧ f (w • P.root i) < 0}) ∧
      (∀ w b, cs.length w < cs.length (w * cs.simple b) ↔ 0 < f (w • P.root b)) := by
  have hone : (invSet P f 1).ncard = 0 := by
    rw [ncard_eq_zero]
    ext i
    simp only [invSet, one_smul, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro h _
    exact not_lt.mpr h.le
  have hmul : ∀ w b, (invSet P f (w * sr P f b)).ncard = (invSet P f w).ncard + 1 ∨
      (invSet P f (w * sr P f b)).ncard + 1 = (invSet P f w).ncard := by
    intro w b
    rcases lt_or_gt_of_ne (smul_root_ne_zero P f hf w b) with h | h
    · exact Or.inr ((ncard_invSet_mul P f hf w b.2).2 h)
    · exact Or.inl ((ncard_invSet_mul P f hf w b.2).1 h)
  obtain ⟨Mx, cs, -, hsimple, hlen⟩ := exists_coxeterSystem_of_exchange (sr P f)
    (fun w => (invSet P f w).ncard) (fun b => ofIdx_mul_self P b)
    (fun a b h => Subtype.ext (ofIdx_injOn_base P f hf a.2 b.2 h)) hone hmul
    (fun x b h => by
      apply exchange P f hf x b
      rcases lt_or_gt_of_ne (smul_root_ne_zero P f hf (x.map (sr P f)).prod b) with h' | h'
      · exact h'
      · have := (ncard_invSet_mul P f hf (x.map (sr P f)).prod b.2).1 h'
        simp only [sr] at h
        omega)
    hgen
  refine ⟨?_, Mx, cs, hsimple, hlen, ?_⟩
  · have hsub : (univ : Set P.weylGroup) ⊆
        cs.wordProd '' {ω | ω.length ≤ Nat.card ι} := by
      intro w _
      obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
      refine ⟨ω, ?_, rfl⟩
      rw [mem_ofPred_eq, ← hω.eq, hlen]
      exact ncard_le_card _
    exact finite_univ_iff.mp (((List.finite_length_le _ _).image _).subset hsub)
  · intro w b
    have e1 : cs.length w = (invSet P f w).ncard := hlen w
    have e2 : cs.length (w * sr P f b) = (invSet P f (w * sr P f b)).ncard := hlen _
    rw [hsimple, e1, e2]
    rcases lt_or_gt_of_ne (smul_root_ne_zero P f hf w b) with h | h
    · have := (ncard_invSet_mul P f hf w b.2).2 h
      change (invSet P f (w * sr P f b)).ncard + 1 = _ at this
      constructor
      · intro h'; omega
      · intro h'; linarith
    · have := (ncard_invSet_mul P f hf w b.2).1 h
      change (invSet P f (w * sr P f b)).ncard = _ at this
      constructor
      · intro _; exact h
      · intro _; omega

end Ordered

/-- The Weyl group of a finite crystallographic root pairing over a linearly ordered field is a
finite Coxeter group on the reflections in the simple roots of a linear form that is nonzero on
every root, with length the number of indivisible positive roots made negative. -/
theorem rootPairingWeylCoxeterStatement_proof :
    RootPairingWeylCoxeterStatement.{u₁, u₂, u₃, u₄} :=
  fun _ _ _ _ _ _ _ _ _ _ _ P _ _ f hf =>
    main_of_generates P f hf (exists_list_prod_ofIdx_baseOf P f hf)

end Langlands.Group
