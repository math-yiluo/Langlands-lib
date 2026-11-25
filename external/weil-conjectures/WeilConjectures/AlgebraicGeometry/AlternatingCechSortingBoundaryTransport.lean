/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Data.Fin.Tuple.Sort
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingIdentity

/-!
# AlternatingCechSortingBoundaryTransport

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
(blueprint: lem-pc-alternating-cech-sorting-boundary-transport)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem sorting_comm (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    cechStableSortingMap X U F S p ≫ S.differential F p =
      S.differential F p ≫ cechStableSortingMap X U F S (p + 1) := by
  have h := (Homotopy.nullHomotopicMap' (cechFirstSortingFamily X U F S)).comm p (p + 1)
  rw [cechFirstSortingIdentity, cechFirstSortingIdentity] at h
  simp only [SiteCechComplex.complex, CochainComplex.of_d,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id] at h
  exact sub_right_inj.mp h

private theorem sorting_apply (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F p) (t : Fin (p + 1) → I) :
    cechStableSortingMap X U F S p s t =
      (Equiv.Perm.sign (Tuple.sort t) : ℤ) •
        F.map (S.indexMap t (Tuple.sort t)).op (s (t ∘ Tuple.sort t)) := by
  classical
  change (∑ σ : Equiv.Perm (Fin (p + 1)), if cechStableSort t σ then _ else 0) = _
  simp only [cechStableSort, ← Tuple.eq_sort_iff]
  simp

open Classical in
private theorem second_apply (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F (p + 1)) (t : Fin (p + 1) → I) :
    cechSecondSortingHom X U F S p s t =
      ∑ a : Fin (p + 1), if cechFirstRepeat (t ∘ Tuple.sort t) a then
        ((Equiv.Perm.sign (Tuple.sort t) : ℤ) * (-1 : ℤ) ^ a.val) •
          F.map (S.indexMap t (cechJunction (Tuple.sort t) (Tuple.sort t) a)).op
            (s (t ∘ cechJunction (Tuple.sort t) (Tuple.sort t) a)) else 0 := by
  classical
  change (∑ σ : Equiv.Perm (Fin (p + 1)), ∑ a : Fin (p + 1),
    if cechStableSort t σ ∧ cechFirstRepeat (t ∘ σ) a then _ else 0) = _
  simp only [cechStableSort, ← Tuple.eq_sort_iff, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem second_sorted (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) : cechSecondSortingHom X U F S p ≫ cechStableSortingMap X U F S p =
      cechSecondSortingHom X U F S p := by
  classical
  apply AddCommGrpCat.ext
  intro s
  funext t
  change cechStableSortingMap X U F S p (cechSecondSortingHom X U F S p s) t = _
  rw [sorting_apply, second_apply, second_apply]
  have hs : Tuple.sort (t ∘ Tuple.sort t) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr (Tuple.monotone_sort t)
  rw [hs]
  simp only [Equiv.Perm.sign_refl, Units.val_one, one_mul, Equiv.coe_refl,
    Function.comp_id]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : cechFirstRepeat (t ∘ Tuple.sort t) a
  · simp only [ha, ite_true, map_zsmul, smul_smul]
    have hj : cechJunction (Tuple.sort t) (Tuple.sort t) a =
        Tuple.sort t ∘ cechJunction (Equiv.refl _) (Equiv.refl _) a := by
      funext k
      simp only [cechJunction, Function.comp_apply, Equiv.refl_apply]
      split_ifs <;> rfl
    rw [hj]
    simp only [Function.comp_assoc]
    congr 1
    have hm : S.indexMap t (Tuple.sort t) ≫
        S.indexMap (t ∘ Tuple.sort t) (cechJunction (Equiv.refl _) (Equiv.refl _) a) =
        S.indexMap t (Tuple.sort t ∘ cechJunction (Equiv.refl _) (Equiv.refl _) a) := by
      exact Subsingleton.elim _ _
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, hm]
  · simp [ha]

open Classical in
/-- Signed stable sorting transports the repeated-tuple boundary.

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equations
20.23.6.1 and 20.23.6.2, transported by signed stable sorting.
Proof: Write kappa for signed stable sorting. The first sorting identity and
square-zero of the differential imply d kappa = kappa d. Stable sorting is
idempotent: sorting a sorted tuple is identity, including its equal-label order.
The repeated-tuple homotopy is the sorted contraction precomposed with kappa:
its formula sorts t and duplicates its first repeat, with the sorting sign.
Duplicating a nondecreasing tuple leaves it nondecreasing. Hence pulling the
sorted contraction back once more by kappa leaves this formula unchanged.
Commute d through kappa in each of the two boundary terms. Both become signed
pullbacks of the boundary at the sorted tuple. The stable-sort filter has one
permutation, characterized by ordering the pairs (t(k), k). Restriction maps
compose by the universal property of the chosen products, so the transports in
these two expansions coincide. Summing over the filter gives the stated formula.
Degree zero has zero contraction. With empty I there are no coordinates.
(blueprint: lem-pc-alternating-cech-sorting-boundary-transport) -/
theorem cechSortingBoundaryTransport (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ)
    (s : S.cochains F p) (t : Fin (p + 1) → I) :
    ((Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p) s t =
      ∑ σ : Equiv.Perm (Fin (p + 1)),
        if cechStableSort t σ then
          (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op
            (((Homotopy.nullHomotopicMap'
              (cechSecondSortingFamily X U F S)).f p) s (t ∘ σ)) else 0 := by
  classical
  have hb : (Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p ≫
      cechStableSortingMap X U F S p =
      (Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p := by
    cases p with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (k₀ := 1) (by rfl)
        (by intro l; change ¬ l + 1 = 0; omega)]
      simp only [cechSecondSortingFamily, SiteCechComplex.complex,
        eqToHom_refl, Category.id_comp]
      rw [Category.assoc, second_sorted]
    | succ p =>
      rw [Homotopy.nullHomotopicMap'_f (k₂ := p) (k₀ := (p + 1) + 1)
        (by rfl) (by rfl)]
      simp only [cechSecondSortingFamily, SiteCechComplex.complex, CochainComplex.of_d,
        eqToHom_refl, Category.id_comp]
      rw [Preadditive.add_comp, Category.assoc, second_sorted, Category.assoc,
        ← sorting_comm, ← Category.assoc, second_sorted]
  change _ = cechStableSortingMap X U F S p
    ((Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p s) t
  exact (congrArg (fun f : S.cochains F p ⟶ S.cochains F p ↦ f s t) hb).symm

end AlgebraicGeometry.Scheme
