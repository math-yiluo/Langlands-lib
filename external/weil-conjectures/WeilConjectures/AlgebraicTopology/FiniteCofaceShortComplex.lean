/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
/-! # The three cochain terms depend on a finite cosimplicial truncation -/
@[expose] public section
universe u v
open CategoryTheory Limits AlgebraicTopology
namespace AlgebraicTopology
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {K L : CosimplicialObject A} {r : ℕ}

/-- A natural map on a finite cosimplicial truncation commutes with its differentials. -/
theorem finiteCofaceMap_comm
    (e : SimplexCategory.Truncated.inclusion r ⋙ K ⟶
      SimplexCategory.Truncated.inclusion r ⋙ L)
    (n m : ℕ) (hn : n ≤ r) (hm : m ≤ r) :
    e.app ⟨SimplexCategory.mk n, hn⟩ ≫ ((alternatingCofaceMapComplex A).obj L).d n m =
      ((alternatingCofaceMapComplex A).obj K).d n m ≫
        e.app ⟨SimplexCategory.mk m, hm⟩ := by
  by_cases h : n + 1 = m
  · subst m
    simp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
      CochainComplex.of_d, AlternatingCofaceMapComplex.objD,
      Preadditive.comp_sum, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    congr 1
    exact (e.naturality (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i) hn hm)).symm
  · rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.shape _ _ _ h,
      HasZeroMorphisms.comp_zero, HasZeroMorphisms.zero_comp]

/-- A map on the finite cosimplicial truncation determines a map of three-term complexes.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2.
Naturality at every coface commutes with the alternating sum defining each differential. For pairs
of degrees not differing by one the differential is zero. The predecessor and successor of q in
the natural-number cochain shape lie through q+1, including predecessor zero at q=0. These
equations verify both short-complex squares for the three displayed components.
(auxiliary; not a blueprint node) -/
noncomputable def finiteCofaceShortComplexMap (q : ℕ)
    (e : SimplexCategory.Truncated.inclusion (q + 1) ⋙ K ⟶
      SimplexCategory.Truncated.inclusion (q + 1) ⋙ L) :
    ((alternatingCofaceMapComplex A).obj K).sc q ⟶
      ((alternatingCofaceMapComplex A).obj L).sc q := by
  have hp : (ComplexShape.up ℕ).prev q ≤ q + 1 := by
    cases q with
    | zero => simp [CochainComplex.prev_nat_zero]
    | succ q => simp only [CochainComplex.prev_nat_succ]; omega
  have hn : (ComplexShape.up ℕ).next q ≤ q + 1 := by
    rw [CochainComplex.next]
  exact {
    τ₁ := e.app ⟨SimplexCategory.mk ((ComplexShape.up ℕ).prev q), hp⟩
    τ₂ := e.app ⟨SimplexCategory.mk q, Nat.le_succ q⟩
    τ₃ := e.app ⟨SimplexCategory.mk ((ComplexShape.up ℕ).next q), hn⟩
    comm₁₂ := finiteCofaceMap_comm e _ _ hp (Nat.le_succ q)
    comm₂₃ := finiteCofaceMap_comm e _ _ (Nat.le_succ q) hn }


end AlgebraicTopology
