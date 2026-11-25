/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise

/-!
# Eventual vanishing of finitely many tensor elements

Source: Stacks Project, Algebra, Tag 05LI, proof of (1).
(blueprint: lem-pc-finite-tensor-vanishing-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleCat

/-- Finitely many elements of a stage module which vanish after tensoring with
the ring colimit all vanish after tensoring with one later ring.

Source: Stacks Project, Algebra, Tag 05LI, proof of (1),
label algebra-lemma-module-map-property-in-colimit.
(blueprint: lem-pc-finite-tensor-vanishing-colimit).

Proof: apply the already-proved directed ring base-change elementwise theorem
`TensorProduct.directedColimitBaseChangeElementwise` to the unit tensor at i.
Its eventual-zero clause gives a later stage for each element. A linear tensor
map induced by F(j to k) preserves zero and unit tensors, so vanishing persists
under further transition. Induction on the finite set combines two stages using
directedness. For the empty set take j=i. No finiteness condition on N is needed. -/
theorem exists_stage_finite_tensor_vanishing
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) (i : I) (N : ModuleCat (F.obj i)) (s : Finset N)
    (hs : ∀ n ∈ s,
      (1 : ↑(colimit F)) ⊗ₜ[F.obj i,CommRingCat.Hom.hom (colimit.ι F i)] n = 0) :
    ∃ (j : I) (hij : i ≤ j), ∀ n ∈ s,
      (1 : F.obj j) ⊗ₜ[F.obj i,CommRingCat.Hom.hom (F.map (homOfLE hij))] n = 0 := by
  classical
  have push (j k : I) (hij : i ≤ j) (hjk : j ≤ k) (n : N)
      (hn : (1 : F.obj j) ⊗ₜ[F.obj i,CommRingCat.Hom.hom (F.map (homOfLE hij))] n = 0) :
      (1 : F.obj k) ⊗ₜ[F.obj i,CommRingCat.Hom.hom
        (F.map (homOfLE (hij.trans hjk)))] n = 0 := by
    let : Algebra (F.obj i) (F.obj j) := (F.map (homOfLE hij)).hom.toAlgebra
    let : Algebra (F.obj i) (F.obj k) :=
      (F.map (homOfLE (hij.trans hjk))).hom.toAlgebra
    let a : F.obj j →ₐ[F.obj i] F.obj k :=
      { (F.map (homOfLE hjk)).hom with
        commutes' := fun x =>
          congrArg (fun f : F.obj i ⟶ F.obj k => f x)
            (F.map_comp (homOfLE hij) (homOfLE hjk)).symm }
    have h := congrArg (LinearMap.rTensor N a.toLinearMap) hn
    simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, map_zero] using h
  have single (n : N) (hn :
      (1 : ↑(colimit F)) ⊗ₜ[F.obj i,CommRingCat.Hom.hom (colimit.ι F i)] n = 0) :
      ∃ (j : I) (hij : i ≤ j),
        (1 : F.obj j) ⊗ₜ[F.obj i,CommRingCat.Hom.hom (F.map (homOfLE hij))] n = 0 := by
    have h := (TensorProduct.directedColimitBaseChangeElementwise F i N).2 i le_rfl
    obtain ⟨j, hij, hj⟩ := h
      ((1 : F.obj i) ⊗ₜ[F.obj i,CommRingCat.Hom.hom (F.map (homOfLE le_rfl))] n)
      (by simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hn)
    exact ⟨j, hij, by
      simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hj⟩
  induction s using Finset.induction_on with
  | empty => exact ⟨i, le_rfl, by simp⟩
  | @insert n s hns ih =>
    obtain ⟨j, hij, hj⟩ := single n (hs n (Finset.mem_insert_self n s))
    obtain ⟨k, hik, hk⟩ := ih (fun m hm => hs m (Finset.mem_insert_of_mem hm))
    obtain ⟨l, hjl, hkl⟩ := IsDirected.directed (r := (· ≤ ·)) j k
    refine ⟨l, hij.trans hjl, ?_⟩
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact push j l hij hjl m hj
    · exact push k l hik hkl m (hk m hm)

end ModuleCat
