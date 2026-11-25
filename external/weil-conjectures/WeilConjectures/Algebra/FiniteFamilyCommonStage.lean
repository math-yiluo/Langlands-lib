/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.NatIso
import Mathlib.Data.Fintype.Basic
/-! # Common stages for a finite family of module map equalities

Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1).
(blueprint: lem-pc-finite-family-common-stage).
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat
/-- A finite family of stage equalities admits one common upper stage.
Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1).
(blueprint: lem-pc-finite-family-common-stage).

Proof: Induct on the finite index type. At each step directedness supplies an upper
bound for the current stage and the previously obtained common stage; functoriality
of extension of scalars transports all earlier equalities to that bound, using the
natural composition isomorphism to identify iterated and direct extensions. In the
empty case choose i, with no equalities to check. No finite presentation is needed.
Source: Stacks Project, Algebra, Tag 05N7, clause (3). -/
theorem exists_common_stage_of_stage_equalities
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (i : I) {T : Type v} [Finite T]
    (M N : T → ModuleCat.{u} (F.obj i))
    (f g : ∀ t, M t ⟶ N t)
    (h : ∀ t, ∃ (j : I) (hij : i ≤ j),
      (extendScalars (F.map (homOfLE hij)).hom).map (f t) =
        (extendScalars (F.map (homOfLE hij)).hom).map (g t)) :
    ∃ (j : I) (hij : i ≤ j), ∀ t,
      (extendScalars (F.map (homOfLE hij)).hom).map (f t) =
        (extendScalars (F.map (homOfLE hij)).hom).map (g t) := by
  classical
  let := Fintype.ofFinite T
  have transport (t : T) (j k : I) (hij : i ≤ j) (hjk : j ≤ k)
      (he : (extendScalars (F.map (homOfLE hij)).hom).map (f t) =
        (extendScalars (F.map (homOfLE hij)).hom).map (g t)) :
      (extendScalars (F.map (homOfLE (hij.trans hjk))).hom).map (f t) =
        (extendScalars (F.map (homOfLE (hij.trans hjk))).hom).map (g t) := by
    let r := (F.map (homOfLE hij)).hom
    let s := (F.map (homOfLE hjk)).hom
    have hr : (F.map (homOfLE (hij.trans hjk))).hom = s.comp r :=
      congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE hij) (homOfLE hjk))
    rw [hr]
    let e := extendScalarsComp r s
    have he' := congrArg (fun a ↦ (extendScalars s).map a) he
    rw [← NatIso.naturality_2 e (f t), ← NatIso.naturality_2 e (g t)]
    exact congrArg (fun a ↦ e.hom.app (M t) ≫ a ≫ e.inv.app (N t)) he'
  have aux (a : Finset T) : ∃ j : I, ∃ hij : i ≤ j, ∀ t ∈ a,
      (extendScalars (F.map (homOfLE hij)).hom).map (f t) =
        (extendScalars (F.map (homOfLE hij)).hom).map (g t) := by
    induction a using Finset.induction_on with
    | empty =>
      exact ⟨i, le_refl i, by simp⟩
    | @insert t a hta ih =>
      obtain ⟨j, hij, hj⟩ := ih
      obtain ⟨l, hil, hl⟩ := h t
      obtain ⟨k, hjk, hlk⟩ := exists_ge_ge j l
      refine ⟨k, hij.trans hjk, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact transport x l k hil hlk hl
      · exact transport x j k hij hjk (hj x hx)
  obtain ⟨j, hij, hj⟩ := aux Finset.univ
  exact ⟨j, hij, fun t ↦ hj t (Finset.mem_univ t)⟩
end ModuleCat
