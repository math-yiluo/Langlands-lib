/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Data.Fin.Tuple.Sort
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingBoundary

/-!
# The first Čech sorting identity

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
(blueprint: lem-pc-alternating-cech-first-sorting-identity)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def partialSortingValue (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p a : ℕ) (s : S.cochains F p) : S.cochains F p := by
  classical
  exact fun t ↦ ∑ σ : Equiv.Perm (Fin (p + 1)),
    ∑ τ : Equiv.Perm (Fin (p + 1)),
      if cechStableSort t σ ∧
          (∀ k, k.val < a → τ k = σ k) ∧
          (∀ i j, a ≤ i.val → i < j → τ i < τ j) then
        (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0

private theorem partialFilter_zero {p : ℕ} (σ τ : Equiv.Perm (Fin (p + 1))) :
    ((∀ k, k.val < 0 → τ k = σ k) ∧
      (∀ i j, 0 ≤ i.val → i < j → τ i < τ j)) ↔ τ = Equiv.refl _ := by
  simp only [Nat.not_lt_zero, false_implies, implies_true, true_and,
    Nat.zero_le, forall_const]
  constructor
  · intro h
    have hs : StrictMono τ := fun _ _ hij ↦ h _ _ hij
    have hm : Monotone τ := hs.monotone
    simpa only [Equiv.Perm.one_def] using (Equiv.Perm.monotone_iff τ).mp hm
  · intro h
    subst τ
    exact strictMono_id

private theorem partialFilter_last {p : ℕ} (σ τ : Equiv.Perm (Fin (p + 1))) :
    ((∀ k, k.val < p + 1 → τ k = σ k) ∧
      (∀ i j, p + 1 ≤ i.val → i < j → τ i < τ j)) ↔ τ = σ := by
  constructor
  · intro h
    apply Equiv.ext
    intro k
    exact h.1 k k.isLt
  · intro h
    subst τ
    exact ⟨fun _ _ ↦ rfl, fun i _ hi _ ↦ (Nat.not_le_of_lt i.isLt hi).elim⟩

private theorem indexMap_id (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (t : Fin (p + 1) → I) : S.indexMap t id = 𝟙 _ := by
  apply Subsingleton.elim

private theorem partialSortingValue_zero (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F p) : partialSortingValue X U F S p 0 s = s := by
  classical
  change (∀ t : Fin (p + 1) → I, F.obj (op (S.W p t))) at s
  funext t
  simp only [partialSortingValue, partialFilter_zero]
  simp only [cechStableSort, ← Tuple.eq_sort_iff]
  simp only [ite_and, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Equiv.Perm.sign_refl, Units.val_one, one_smul]
  change F.map (S.indexMap t id).op (s t) = s t
  rw [indexMap_id]
  simp

private theorem partialSortingValue_last (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F p) :
    partialSortingValue X U F S p (p + 1) s = cechStableSortingMap X U F S p s := by
  classical
  change (∀ t : Fin (p + 1) → I, F.obj (op (S.W p t))) at s
  funext t
  change (∑ σ : Equiv.Perm (Fin (p + 1)),
    ∑ τ : Equiv.Perm (Fin (p + 1)),
      if cechStableSort t σ ∧
          (∀ k, k.val < p + 1 → τ k = σ k) ∧
          (∀ i j, p + 1 ≤ i.val → i < j → τ i < τ j) then
        (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0) =
    ∑ σ : Equiv.Perm (Fin (p + 1)),
      if cechStableSort t σ then
        (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (s (t ∘ σ)) else 0
  simp only [partialFilter_last]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : cechStableSort t σ <;> simp [h]

private theorem telescope {A : Type*} [AddCommGroup A] (f : ℕ → A) (n : ℕ) :
    (∑ a : Fin n, (f a.val - f (a.val + 1))) = f 0 - f n := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ f i - f (i + 1)) n]
  exact Finset.sum_range_sub' f n

/-- The first sorting operator contracts identity minus stable sorting.

Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-first-sorting-identity)

Proof: The filter selects the unique permutation sorting the pairs (t(k), k)
lexicographically. For each a, its partial-sort filter selects the unique permutation
with the specified prefix and increasing unused original positions. Thus the finite
sum is exactly the junction formula of 20.23.6.1, with no multiplicities.
Expand the two differentials at an arbitrary tuple t. Label every occurrence by its
original position, even when values coincide. Deleting a label j from a sorted tuple
removes that label from its stable sorting permutation and renumbers labels above j.
Do the same in each partial permutation. For a permutation π, deletion of its r-th
position changes its sign by (-1)^(r+π(r)). This follows by moving that position and
its value to the last positions and then restricting the permutation.
Pair a deletion of a nonjunction label in the junction sum with the term in the
junction sum for the corresponding face of t. If the deleted label is in the sorted
prefix the junction number drops by one; if it is in the remaining tail it stays the
same. The deletion-sign formula gives opposite coefficients in the two expansions.
Both transports have the same composites with every projection, hence are equal by
S.universal. The two deletions of the junction label compare consecutive partial
permutations; their terms telescope as a ranges from zero to p. The initial partial
permutation is identity, giving the original cochain with coefficient 1; the final
one is the stable sorting permutation, giving minus its signed pullback. This proves
the identity coordinatewise. In degree zero the incoming differential is zero and
stable sorting is identity. If I is empty every cochain group is a zero object. -/
theorem cechFirstSortingIdentity (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    (Homotopy.nullHomotopicMap' (cechFirstSortingFamily X U F S)).f p =
      𝟙 (S.cochains F p) - cechStableSortingMap X U F S p := by
  classical
  cases p with
  | zero =>
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (k₀ := 1) (by rfl)
      (by intro l; change ¬ l + 1 = 0; omega)]
    simp only [cechFirstSortingFamily, SiteCechComplex.complex,
      eqToHom_refl, Category.id_comp]
    apply AddCommGrpCat.ext
    intro s
    funext t
    change (cechFirstSortingHom X U F S 0 (S.differential F 0 s)) t =
      s t - (cechStableSortingMap X U F S 0 s) t
    change (∀ t : Fin (0 + 1) → I, F.obj (op (S.W 0 t))) at s
    simp only [homOfLE_leOfHom, Nat.reduceAdd, cechFirstSortingHom, Finset.univ_unique,
      Equiv.Perm.default_eq, Fin.default_eq_zero, Fin.isValue, cechStableSort,
      isEmpty_Prop, not_lt, le_of_subsingleton, IsEmpty.forall_iff, implies_true, and_true,
      cechPartialSort, Fin.val_eq_zero, lt_self_iff_false, Std.le_refl, and_self,
      Int.reduceNeg, pow_zero, one_mul, Finset.sum_ite_irrel, Finset.sum_singleton,
      Equiv.Perm.sign_one, Units.val_one, one_smul, Finset.sum_const_zero,
      Equiv.Perm.coe_one, CompTriple.comp_eq, ConcreteCategory.hom_ofHom,
      SiteCechComplex.differential, cechStableSortingMap, Function.comp_id]
    change (if Monotone t then
      F.map (S.indexMap t (cechJunction 1 1 0)).op
        (S.differentialValue F 0 s (t ∘ cechJunction 1 1 0)) else 0) =
      s t - (if Monotone t then F.map (S.indexMap t id).op (s t) else 0)
    have hm : Monotone t := by
      intro i j _
      have h : i = j := by omega
      subst j
      rfl
    rw [ite_eq_left hm, ite_eq_left hm, indexMap_id]
    erw [op_id, F.map_id]
    erw [ConcreteCategory.id_apply]
    rw [sub_self]
    have hd : S.differentialValue F 0 s (t ∘ cechJunction 1 1 0) = 0 := by
      change (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
        F.map (S.indexMap (t ∘ cechJunction 1 1 0) j.succAbove).op
          (s ((t ∘ cechJunction 1 1 0) ∘ j.succAbove))) = 0
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
        neg_smul, one_smul, ← sub_eq_add_neg]
      have hJ : cechJunction (1 : Equiv.Perm (Fin 1)) 1 0 =
          fun _ : Fin 2 ↦ (0 : Fin 1) := by
        funext k
        omega
      rw [hJ, sub_eq_zero]
      apply congrArg (fun f : S.W 1 (fun _ ↦ t 0) ⟶ S.W 0 (fun _ ↦ t 0) ↦
        F.map f.op (s (fun _ ↦ t 0)))
      exact Subsingleton.elim _ _
    rw [hd]
    exact map_zero _
  | succ p =>
    rw [Homotopy.nullHomotopicMap'_f (k₂ := p) (k₀ := (p + 1) + 1) (by rfl) (by rfl)]
    simp only [cechFirstSortingFamily, SiteCechComplex.complex, CochainComplex.of_d,
      eqToHom_refl, Category.id_comp]
    apply AddCommGrpCat.ext
    intro s
    funext t
    change (cechFirstSortingHom X U F S (p + 1)
      (S.differential F (p + 1) s)) t +
      (S.differential F p (cechFirstSortingHom X U F S p s)) t =
      s t - (cechStableSortingMap X U F S (p + 1) s) t
    have hb := cechFirstSortingBoundary X U F S p s t
    change _ = ∑ a : Fin (p + 2),
      (partialSortingValue X U F S (p + 1) a.val s t -
        partialSortingValue X U F S (p + 1) (a.val + 1) s t) at hb
    rw [hb, telescope (fun a ↦ partialSortingValue X U F S (p + 1) a s t) (p + 2)]
    rw [partialSortingValue_zero, partialSortingValue_last]

end AlgebraicGeometry.Scheme
