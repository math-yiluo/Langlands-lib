/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-! # Free-module resolution of a set Cech nerve
Source: literature/stacks-project/hypercovering.tex, Tag 01GC (blueprint:
lem-weil-pbc-set-cech-nerve-free-resolution).
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicTopology

universe u v

variable {R : Type u} [Ring R] {A : Type v} {B : Type v} (f : A → B)

/-- The fibrewise Cech nerve in degree `n` of a map of sets.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
def setCechNerve (f : A → B) (n : ℕ) : Type v :=
  {x : Fin (n + 1) → A // ∀ i, f (x i) = f (x 0)}

/-- The free `R`-module on the degree-`n` Cech nerve.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
abbrev setCechNerveModule (R : Type u) [Ring R] (f : A → B) (n : ℕ) :
    Type (max u v) := setCechNerve f n →₀ R

/-- The face map deleting coordinate `j`.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
def setCechFace (f : A → B) {n : ℕ} (j : Fin (n + 2)) :
    setCechNerve f (n + 1) → setCechNerve f n := by
  intro x
  let y : Fin (n + 1) → A := fun i => x.1 (Fin.succAbove j i)
  refine ⟨y, ?_⟩
  intro i
  have hi := x.2 (Fin.succAbove j i)
  have h0 := x.2 (Fin.succAbove j 0)
  simpa [y] using hi.trans h0.symm

/-- The alternating face differential on free modules of the Cech nerve.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
noncomputable def setCechDifferential (R : Type u) [Ring R] (f : A → B) (n : ℕ) :
    setCechNerveModule R f (n + 1) →ₗ[R] setCechNerveModule R f n :=
  Finsupp.lift _ _ _ (fun x =>
    ∑ j : Fin (n + 2), ((-1 : R) ^ (j : ℕ)) •
      Finsupp.single (setCechFace f j x) (1 : R))

/-- The augmentation induced by `f` on free modules.
Source: Stacks Project, Tag 01GC; (blueprint: lem-weil-pbc-set-cech-nerve-free-resolution). -/
noncomputable def setCechAugmentation (R : Type u) [Ring R] (f : A → B) :
    setCechNerveModule R f 0 →ₗ[R] B →₀ R :=
  Finsupp.lift _ _ _ (fun x => Finsupp.single (f ((x : setCechNerve f 0).1 0)) (1 : R))

private theorem free_ext {X : Type v} {M : Type*} [AddCommGroup M] [Module R M]
    {g h : (X →₀ R) →ₗ[R] M}
    (heq : ∀ x, g (Finsupp.single x 1) = h (Finsupp.single x 1)) : g = h := by
  apply Finsupp.lhom_ext
  intro x r
  have hs : Finsupp.single x r = r • Finsupp.single x (1 : R) := by simp
  rw [hs, map_smul, map_smul, heq]

private theorem differential_single (n : ℕ) (x : setCechNerve f (n + 1)) :
    setCechDifferential R f n (Finsupp.single x 1) =
      ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) •
        Finsupp.single (setCechFace f j x) 1 := by
  classical
  simp [setCechDifferential]

private theorem augmentation_single (x : setCechNerve f 0) :
    setCechAugmentation R f (Finsupp.single x 1) =
      Finsupp.single (f (x.1 0)) 1 := by
  classical
  simp [setCechAugmentation]

private def prepend (s : B → A) (hs : ∀ b, f (s b) = b) {n : ℕ}
    (x : setCechNerve f n) : setCechNerve f (n + 1) := by
  refine ⟨Fin.cons (s (f (x.1 0))) x.1, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simpa using (x.2 j).trans (hs (f (x.1 0))).symm

private theorem face_prepend_zero (s : B → A) (hs : ∀ b, f (s b) = b)
    {n : ℕ} (x : setCechNerve f n) : setCechFace f 0 (prepend f s hs x) = x := by
  apply Subtype.ext
  funext i
  simp [setCechFace, prepend]

private theorem face_prepend_succ (s : B → A) (hs : ∀ b, f (s b) = b)
    {n : ℕ} (x : setCechNerve f (n + 1)) (j : Fin (n + 2)) :
    setCechFace f j.succ (prepend f s hs x) = prepend f s hs (setCechFace f j x) := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [setCechFace, prepend, x.2 (j.succAbove 0)]
  · simp [setCechFace, prepend, Fin.succ_succAbove_succ]

private noncomputable def homotopy (s : B → A) (hs : ∀ b, f (s b) = b) (n : ℕ) :
    setCechNerveModule R f n →ₗ[R] setCechNerveModule R f (n + 1) :=
  Finsupp.lift _ _ _ (fun x => Finsupp.single (prepend f s hs x) 1)

private theorem homotopy_single (s : B → A) (hs : ∀ b, f (s b) = b)
    (n : ℕ) (x : setCechNerve f n) :
    homotopy (R := R) f s hs n (Finsupp.single x 1) =
      Finsupp.single (prepend f s hs x) 1 := by
  classical
  simp [homotopy]

private theorem homotopy_identity (s : B → A) (hs : ∀ b, f (s b) = b) (n : ℕ) :
    (setCechDifferential R f (n + 1)).comp (homotopy f s hs (n + 1)) +
      (homotopy f s hs n).comp (setCechDifferential R f n) = LinearMap.id := by
  classical
  apply free_ext
  intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    homotopy_single, differential_single, map_sum, map_smul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, face_prepend_zero,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, face_prepend_succ]
  rw [Finset.sum_neg_distrib]
  abel

private theorem face_face (n : ℕ) (x : setCechNerve f (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 3)) (h : j.val ≤ i.val) :
    setCechFace f i (setCechFace f j x) =
      setCechFace f (Fin.castLT j (lt_of_le_of_lt h i.isLt))
        (setCechFace f i.succ x) := by
  apply Subtype.ext
  funext k
  change x.1 (j.succAbove (i.succAbove k)) =
    x.1 (i.succ.succAbove ((Fin.castLT j _).succAbove k))
  apply congrArg x.1
  apply Fin.ext
  simp only [Fin.succAbove]
  split_ifs <;> simp_all [Fin.lt_def] <;> omega

private theorem differential_squared (n : ℕ) :
    (setCechDifferential R f n).comp (setCechDifferential R f (n + 1)) = 0 := by
  classical
  apply free_ext
  intro x
  simp only [LinearMap.comp_apply, differential_single, map_sum, map_smul,
    Finset.smul_sum, smul_smul, LinearMap.zero_apply]
  rw [Finset.sum_comm, ← Finset.sum_product', Finset.univ_product_univ]
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | ij.2.val ≤ ij.1.val}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.isLt),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp at hij'
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    rw [face_face f n x i j (Finset.mem_filter.mp hij).2]
    simp only [φ, Fin.val_succ, Fin.val_castLT, pow_succ,
      mul_neg, neg_mul, mul_one, neg_smul, neg_neg]
    congr 1
    rw [← pow_add, ← pow_add, Nat.add_comm]

private def vertex (a : A) : setCechNerve f 0 := ⟨fun _ => a, fun _ => rfl⟩

private noncomputable def sectionMap (s : B → A) :
    (B →₀ R) →ₗ[R] setCechNerveModule R f 0 :=
  Finsupp.lift _ _ _ (fun b => Finsupp.single (vertex f (s b)) 1)

private theorem sectionMap_single (s : B → A) (b : B) :
    sectionMap (R := R) f s (Finsupp.single b 1) =
      Finsupp.single (vertex f (s b)) 1 := by
  classical
  simp [sectionMap]

private theorem augmentation_section (s : B → A) (hs : ∀ b, f (s b) = b) :
    (setCechAugmentation R f).comp (sectionMap f s) = LinearMap.id := by
  apply free_ext
  intro b
  simp [LinearMap.comp_apply, sectionMap_single, augmentation_single, vertex, hs]

private theorem augmentation_differential :
    (setCechAugmentation R f).comp (setCechDifferential R f 0) = 0 := by
  classical
  apply free_ext
  intro x
  simp [LinearMap.comp_apply, differential_single, Fin.sum_univ_two,
    augmentation_single, setCechFace, x.2 1]

private theorem homotopy_identity_zero (s : B → A) (hs : ∀ b, f (s b) = b) :
    (setCechDifferential R f 0).comp (homotopy f s hs 0) +
      (sectionMap f s).comp (setCechAugmentation R f) = LinearMap.id := by
  classical
  apply free_ext
  intro x
  have hx : setCechFace f (1 : Fin 2) (prepend f s hs x) =
      vertex f (s (f (x.1 0))) := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    rfl
  simp [LinearMap.comp_apply, homotopy_single, differential_single, Fin.sum_univ_two,
    face_prepend_zero, hx, augmentation_single, sectionMap_single]

private theorem range_eq_ker_of_contraction
    {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (d : N →ₗ[R] M) (e : M →ₗ[R] P) (h : M →ₗ[R] N) (k : P →ₗ[R] M)
    (hde : e.comp d = 0) (hcontract : d.comp h + k.comp e = LinearMap.id) :
    LinearMap.range d = LinearMap.ker e := by
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    change e (d y) = 0
    exact LinearMap.congr_fun hde y
  · intro z hz
    change e z = 0 at hz
    refine ⟨h z, ?_⟩
    have hc := LinearMap.congr_fun hcontract z
    simpa [hz] using hc

/-- The augmented free-module Cech nerve is a resolution of the free module on the target.
Source: Stacks Project, Tag 01GC and Tag 03AT
(blueprint: lem-weil-pbc-set-cech-nerve-free-resolution).
Proof: choose a section of the surjection and prefix it to tuples to obtain a contracting
homotopy; alternating-face terms cancel in pairs, yielding the chain identities and exactness.
-/
theorem setCechNerve_free_resolution
    (R : Type u) [Ring R] (f : A → B) (hsurj : Function.Surjective f) :
    (∀ n : ℕ, (setCechDifferential R f n).comp (setCechDifferential R f (n + 1)) = 0) ∧
    (setCechAugmentation R f).comp (setCechDifferential R f 0) = 0 ∧
    LinearMap.range (setCechAugmentation R f) = ⊤ ∧
    LinearMap.range (setCechDifferential R f 0) = LinearMap.ker (setCechAugmentation R f) ∧
    (∀ n : ℕ, LinearMap.range (setCechDifferential R f (n + 1)) =
      LinearMap.ker (setCechDifferential R f n)) := by
  classical
  obtain ⟨s, hs⟩ := hsurj.hasRightInverse
  refine ⟨differential_squared f, augmentation_differential f, ?_, ?_, ?_⟩
  · apply LinearMap.range_eq_top.mpr
    intro y
    refine ⟨sectionMap f s y, ?_⟩
    exact LinearMap.congr_fun (augmentation_section f s hs) y
  · exact range_eq_ker_of_contraction (setCechDifferential R f 0)
      (setCechAugmentation R f) (homotopy f s hs 0) (sectionMap f s)
      (augmentation_differential f) (homotopy_identity_zero f s hs)
  · intro n
    exact range_eq_ker_of_contraction (setCechDifferential R f (n + 1))
      (setCechDifferential R f n) (homotopy f s hs (n + 1)) (homotopy f s hs n)
      (differential_squared f n) (homotopy_identity f s hs n)

end AlgebraicTopology
