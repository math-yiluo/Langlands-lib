/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Constant sheaves and equivalences of sites

For an equivalence of sites `e : C ≌ D`, the equivalence of sheaf categories
`CategoryTheory.Equivalence.sheafCongr` commutes with the constant sheaf functors
(`CategoryTheory.Equivalence.constantSheafSheafCongrIso`); in particular a sheaf is constant if
and only if its transport is (`CategoryTheory.Sheaf.isConstant_sheafCongr_functor_iff`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (e : C ≌ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [e.inverse.IsDenseSubsite K J]
  (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The sections of the transport of a sheaf `G` along an equivalence of sites over `Y : D`
are the sections of `G` over `e.inverse.obj Y`. -/
def Equivalence.sheafCongrFunctorCompSheafSectionsObjIso (Y : D) :
    (e.sheafCongr J K A).functor ⋙ (sheafSections K A).obj (Opposite.op Y) ≅
      (sheafSections J A).obj (Opposite.op (e.inverse.obj Y)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The transport of sheaves along an equivalence of sites commutes with the constant sheaf
functors: both `constantSheaf J A ⋙ functor` and `constantSheaf K A` are left adjoint to
global sections over a terminal object. -/
noncomputable def Equivalence.constantSheafSheafCongrIso {T : C} (hT : IsTerminal T) :
    constantSheaf J A ⋙ (e.sheafCongr J K A).functor ≅ constantSheaf K A :=
  have hT' : IsTerminal (e.functor.obj T) := hT.isTerminalObj e.functor
  (((constantSheafAdj J A hT).comp (e.sheafCongr J K A).toAdjunction).ofNatIsoRight
    (NatIso.ofComponents (F := (e.sheafCongr J K A).inverse ⋙
      (sheafSections J A).obj (Opposite.op T))
      (G := (sheafSections K A).obj (Opposite.op (e.functor.obj T)))
      (fun _ ↦ Iso.refl _) (fun _ ↦ by
        dsimp
        rw [Category.comp_id, Category.id_comp]
        rfl))).leftAdjointUniq (constantSheafAdj K A hT')

variable {J K A}

/-- The transport of a constant sheaf along an equivalence of sites is constant. -/
lemma Sheaf.isConstant_sheafCongr_functor {T : C} (hT : IsTerminal T)
    (G : Sheaf J A) [G.IsConstant J] :
    ((e.sheafCongr J K A).functor.obj G).IsConstant K := by
  obtain ⟨a, ⟨i⟩⟩ := G.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso K
    ((e.sheafCongr J K A).functor.mapIso i.symm ≪≫ (e.constantSheafSheafCongrIso J K A hT).app a)

/-- A sheaf is constant if and only if its transport along an equivalence of sites is. -/
lemma Sheaf.isConstant_sheafCongr_functor_iff {T : C} (hT : IsTerminal T) (G : Sheaf J A) :
    ((e.sheafCongr J K A).functor.obj G).IsConstant K ↔ G.IsConstant J := by
  refine ⟨fun h ↦ ?_, fun _ ↦ Sheaf.isConstant_sheafCongr_functor e hT G⟩
  have hT' : IsTerminal (e.functor.obj T) := hT.isTerminalObj e.functor
  have : e.symm.inverse.IsDenseSubsite J K := inferInstanceAs (e.functor.IsDenseSubsite J K)
  have : ((e.symm.sheafCongr K J A).functor.obj ((e.sheafCongr J K A).functor.obj G)).IsConstant
      J :=
    Sheaf.isConstant_sheafCongr_functor e.symm hT' _
  have : (((e.sheafCongr J K A).functor ⋙ (e.sheafCongr J K A).inverse).obj G).IsConstant J :=
    this
  exact Sheaf.isConstant_congr J ((e.sheafCongr J K A).unitIso.app G).symm

end CategoryTheory
