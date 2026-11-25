/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Compact maps into a coproduct have finite thick support

Source: Stacks Project, Derived Categories, Tag 09SP, with the stage notation of
Tag 09SN (blueprint: lem-sc-compact-coproduct-finite-thick-support).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Enlarging a finite generator support enlarges its thick envelope.
Source: Stacks Project, Tag 09SP
(blueprint: lem-sc-compact-coproduct-finite-thick-support).
Proof: include the smaller coproduct into the larger and retract by zero on the
extra summands. Retract closure and minimality of the thick envelope give inclusion. -/
theorem finite_thick_mono
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{w} C]
    {I : Type w} (E : I → C) {S U : Finset I} (hSU : S ⊆ U) :
    (ObjectProperty.singleton (∐ fun i : {i : I // i ∈ S} ↦ E i.val)).triangEnvelope ≤
      (ObjectProperty.singleton (∐ fun i : {i : I // i ∈ U} ↦ E i.val)).triangEnvelope := by
  classical
  let A := fun i : {i : I // i ∈ S} ↦ E i.val
  let B := fun i : {i : I // i ∈ U} ↦ E i.val
  let a : ∐ A ⟶ ∐ B := Sigma.desc (fun i ↦ Sigma.ι B ⟨i.val, hSU i.property⟩)
  let b : ∐ B ⟶ ∐ A := Sigma.desc (fun i ↦
    if h : i.val ∈ S then Sigma.ι A ⟨i.val, h⟩ else 0)
  have hab : a ≫ b = 𝟙 _ := by
    apply Sigma.hom_ext
    intro i
    simp [a, b, i.property]
  refine (ObjectProperty.triangEnvelope_le_iff (ObjectProperty.singleton (∐ A))
    (Q := (ObjectProperty.singleton (∐ B)).triangEnvelope)).mpr ?_
  refine ObjectProperty.singleton_le_iff.mpr ?_
  exact (ObjectProperty.singleton (∐ B)).triangEnvelope.prop_of_retract
    (⟨a, b, hab⟩ : Retract (∐ A) (∐ B))
    ((ObjectProperty.singleton (∐ B)).le_triangEnvelope _ (by simp))

/-- A compact-source map into a coproduct of shifted generators has finite thick support.
Source: Stacks Project, Derived Categories, Tag 09SP, initial-stage argument.
(blueprint: lem-sc-compact-coproduct-finite-thick-support).

Proof: compactness writes the map as a finite sum of maps to individual summands.
Take the image of the finite support in the generator index set. Each corresponding
unshifted generator is a retract of the coproduct over this image, hence belongs to
its thick envelope. Closure under shifts and finite sums puts the finite supported
coproduct in the same envelope. Its canonical inclusion into the original coproduct
and the finite sum of the supported components give the required factorization. -/
theorem compact_coproduct_finite_thick_support
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{w} C]
    {I J : Type w} (E : I → C) (i : J → I) (m : J → ℤ)
    (K : C) (hK : IsCompactObject K) (f : K ⟶ ∐ fun j : J ↦ (E (i j))⟦m j⟧) :
    ∃ (S : Finset I) (Q : C) (a : K ⟶ Q)
        (b : Q ⟶ ∐ fun j : J ↦ (E (i j))⟦m j⟧),
      (ObjectProperty.singleton (∐ fun i : {i : I // i ∈ S} ↦ E i.val)).triangEnvelope Q ∧
        a ≫ b = f := by
  classical
  let A := fun j : J ↦ (E (i j))⟦m j⟧
  let c := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp K (Sigma.ι A j))
  obtain ⟨x, hx⟩ := (hK J A).2 f
  let S := x.support.image i
  let B := fun j : {j : J // j ∈ x.support} ↦ A j.val
  let a : K ⟶ ∐ B := ∑ j ∈ x.support,
    if h : j ∈ x.support then x j ≫ Sigma.ι B ⟨j, h⟩ else 0
  let b : ∐ B ⟶ ∐ A := Sigma.desc (fun j ↦ Sigma.ι A j.val)
  let P := (ObjectProperty.singleton (∐ fun k : {k : I // k ∈ S} ↦ E k.val)).triangEnvelope
  have hgen : P (∐ fun k : {k : I // k ∈ S} ↦ E k.val) :=
    (ObjectProperty.singleton _).le_triangEnvelope _ (by simp)
  have hB : ∀ j, P (B j) := by
    intro j
    have hi : i j.val ∈ S := Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩
    have hE : P (E (i j.val)) := by
      apply P.prop_of_retract
        (⟨Sigma.ι (fun k : {k : I // k ∈ S} ↦ E k.val) ⟨i j.val, hi⟩,
          Sigma.π (fun k : {k : I // k ∈ S} ↦ E k.val) ⟨i j.val, hi⟩, by simp⟩ :
          Retract (E (i j.val)) (∐ fun k : {k : I // k ∈ S} ↦ E k.val)) hgen
    exact P.le_shift (m j.val) _ hE
  have hQ : P (∐ B) := by
    apply P.prop_of_iso ((biproduct.isoCoproduct B).symm ≪≫ biproduct.isoProduct B).symm
    exact P.prop_product hB
  refine ⟨S, ∐ B, a, b, hQ, ?_⟩
  have hc : c x = ∑ j ∈ x.support, x j ≫ Sigma.ι A j := by
    conv_lhs => rw [← DirectSum.sum_support_of x]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact DirectSum.toAddMonoid_of _ _ _
  rw [← hx]
  change a ≫ b = c x
  rw [hc]
  dsimp [a]
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j hj
  simp [hj, b, Category.assoc]

end CategoryTheory
