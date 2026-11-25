/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Cofinality of affine pointed étale neighbourhoods

Source: Weil conjectures blueprint, chapter `chap-Cohomology-of-torsion-sheaves-on-curves`, unit
`lem-sc-second-kummer-divisors` (blueprint: lemma-weil-pbc-affine-neighbourhood-cofinal); Stacks
Project, Tags 04HX and 0BUC.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The full subcategory of affine pointed étale neighbourhoods of a geometric point is
initial; its opposite inclusion is final, so computes the same opposite-indexed stalk colimit.
Source: blueprint `lem-sc-second-kummer-divisors` (blueprint:
lemma-weil-pbc-affine-neighbourhood-cofinal), Stacks Project, proof of Tag 04HX and the dual of Tag
0BUC, with Tag 04E7.

Proof:
1. For each pointed neighbourhood, choose an affine open containing its geometric point
   and lift the point to that open. Its inclusion is a point-preserving refinement
   (`lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`), so each comma category
   of affine neighbourhoods mapping to a fixed neighbourhood is nonempty.
2. Given two comma objects, cofilteredness of the ambient pointed neighbourhood category
   (`definition-torsion-sheaves--3`) gives a common refinement.
   Equalize its two composites to the fixed neighbourhood, then shrink the resulting
   refinement to an affine open as in step 1. Fullness gives arrows from this affine
   comma object to both original comma objects, hence a connecting zigzag. Thus every
   comma category is connected, and the inclusion is initial
   (`lem-weil-pbc-colimit-initial-full-subcategory`).
3. Passing to opposites makes the inclusion final. The final-functor colimit comparison
   identifies the affine-indexed colimit with the full stalk colimit
   (`lem-weil-pbc-colimit-initial-full-subcategory`). -/
theorem affinePointedNeighbourhoods_initial_and_final_op
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Functor.Initial
      (ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)) ∧
    Functor.Final
      (ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).op := by
  have h : Functor.Initial
      (ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)) := by
    apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    intro n
    induction n with | @mk X x
    cases X with | _ Y f
    obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
    dsimp at y hy
    obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
        (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
      obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
        (x := y.base default) (U := ⊤) (by simp)
      refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    refine ⟨⟨Functor.elementsMk _ (Etale.mk (j ≫ f))
      (Over.homMk y'), by change IsAffine (Spec (.of R)); infer_instance⟩, ?_⟩
    exact ⟨⟨MorphismProperty.Over.homMk j rfl (by simp), by cat_disch⟩⟩
  exact ⟨h, inferInstance⟩

end AlgebraicGeometry.Scheme
