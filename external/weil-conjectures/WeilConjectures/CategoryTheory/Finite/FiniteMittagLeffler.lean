/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDerivedProductRepresentation
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.AlgebraicGeometry.DeligneLaumon.SequentialDerivedInverseLimit
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Mittag--Leffler vanishing for finite abelian groups

Source: blueprint sec-deligne-laumon-a1/sk-l-dl-a1-endpoints, order 2731;
Stacks Project, Tags 07KW and 07KY (blueprint: lem-weil-pbc-mittag-leffler).
The natural index n denotes positive level n+1. Canonical maps in D(Ab) are specified
by their limit-projection equations, exactly as in `milnor_shortExact`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The first right derived inverse limit with the recorded canonical instance parameters.
This abbreviates the existing right derived functor; it does not replace it by a cokernel.
Source: Stacks Tag 07KW (blueprint: lem-weil-pbc-mittag-leffler). -/
abbrev firstDerivedLimitAb (B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : AddCommGrpCat.{u} :=
  letI := roosTowerEnoughInjectives
  letI := roosLimitAdditive
  ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj B

/-- Finite abelian groups form an ML tower and its first derived inverse limit vanishes.
Source: Stacks Tags 02N0, 0597 and 07KW (blueprint: lem-weil-pbc-mittag-leffler).
Proof: for a fixed level the descending images are subgroups of a finite group.
Choose an image of minimum cardinality; all later images equal it. For any tuple y,
the finite nonempty sets of prefix solutions x_j-f_j(x_(j+1))=y_j form an ML tower:
choose the last x to be zero and solve backwards; descending finite images stabilize.
By Mathlib's finite cofiltered-system theorem there is a compatible family of prefixes,
hence a full solution. Thus roosMap is surjective. The cokernel description in
lem-pc-derived-limit-roos-abelian-groups identifies R¹ lim with zero. -/
theorem finiteTower_mittagLeffler_vanishing (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : ∀ n : ℕᵒᵖ, Finite (A.obj n)) :
    (A ⋙ forget AddCommGrpCat).IsMittagLeffler ∧
      IsZero (firstDerivedLimitAb A) := by
  classical
  let (n : ℕᵒᵖ) : Finite (A.obj n) := hA n
  refine ⟨?_, ?_⟩
  · exact (A ⋙ forget AddCommGrpCat).isMittagLeffler_of_exists_finite_range
      (fun n ↦ ⟨n, 𝟙 n, by
        have : Finite ((A ⋙ forget AddCommGrpCat).obj n) := hA n
        exact Set.toFinite _⟩)
  · have hsurj : Function.Surjective (roosMap A) := by
      intro y
      let Y (n : ℕ) := Pi.π (fun n : ℕ ↦ A.obj (op n)) n y
      let f (n : ℕ) := A.map (homOfLE (Nat.le_succ n)).op
      let E (n : ℕ) := {x : ∀ j : Fin (n + 1), A.obj (op j.val) //
        ∀ j : Fin n, x ⟨j.val, by omega⟩ -
          f j.val (x ⟨j.val + 1, by omega⟩) = Y j.val}
      let r (n : ℕ) : E (n + 1) → E n := fun x ↦
        ⟨fun j ↦ x.val ⟨j.val, by omega⟩,
          fun j ↦ x.prop ⟨j.val, by omega⟩⟩
      let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence (fun n ↦ ↾(r n))
      have hnonempty (n : ℕ) : Nonempty (E n) := by
        let x : ∀ j : Fin (n + 1), A.obj (op j.val) :=
          Fin.reverseInduction 0 (fun j z ↦ Y j.val + f j.val z)
        refine ⟨⟨x, fun j ↦ ?_⟩⟩
        have h := @Fin.reverseInduction_castSucc n
          (fun j ↦ A.obj (op j.val)) 0 (fun j z ↦ Y j.val + f j.val z) j
        simp only [Fin.val_castSucc, Fin.val_succ] at h
        change x ⟨j.val, _⟩ = Y j.val + f j.val (x ⟨j.val + 1, _⟩) at h
        rw [h]
        exact add_sub_cancel_right _ _
      have : ∀ n : ℕᵒᵖ, Nonempty (F.obj n) := fun n ↦ hnonempty n.unop
      have : ∀ n : ℕᵒᵖ, Finite (F.obj n) := fun n ↦ by
        change Finite (E n.unop)
        dsimp only [E]
        infer_instance
      obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system F
      let x (n : ℕ) := (s (op n)).val ⟨n, Nat.lt_succ_self n⟩
      have hx (n : ℕ) : x n - f n (x (n + 1)) = Y n := by
        have he := congrArg (fun z : E n ↦ z.val ⟨n, Nat.lt_succ_self n⟩)
          (hs (homOfLE (Nat.le_succ n)).op)
        simp only [F, Functor.ofOpSequence_map_homOfLE_succ] at he
        change (s (op (n + 1))).val ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ = x n at he
        have heq := (s (op (n + 1))).prop ⟨n, Nat.lt_succ_self n⟩
        change (s (op (n + 1))).val ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ -
          f n (x (n + 1)) = Y n at heq
        rwa [he] at heq
      refine ⟨(Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).symm x, ?_⟩
      apply (Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).injective
      funext n
      simp only [Concrete.productEquiv_apply_apply]
      change ((roosMap A ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n)
        ((Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).symm x)) = _
      simpa [roosMap, towerTransitionEndomorphism, towerProductShift, Y, f] using hx n
    have : Epi (roosMap A) := (AddCommGrpCat.epi_iff_surjective _).mpr hsurj
    obtain ⟨_, e₁, _⟩ := derivedLimitRoosAbelianGroups.{u}.2
    exact (isZero_cokernel_of_epi (roosMap A)).of_iso (e₁ A)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
