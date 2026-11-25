/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Constant sheaves, localization of sites and pullback

The constant sheaf functor commutes with localization of a site at an object
(`CategoryTheory.GrothendieckTopology.overPullbackConstantSheafIso`); in particular the
restriction of a constant sheaf to a localized site is constant
(`CategoryTheory.Sheaf.isConstant_over`).

More generally, the constant sheaf functor commutes with the pullback of sheaves along
a continuous functor of sites which preserves a terminal object
(`CategoryTheory.Functor.sheafPullbackCommuteConstant`); in particular the pullback of a
constant sheaf is constant (`CategoryTheory.Sheaf.isConstant_sheafPullback`).

This file imports both `Mathlib.CategoryTheory.Sites.ConstantSheaf` and
`Mathlib.CategoryTheory.Sites.Over` since neither imports the other, and additionally
`Mathlib.CategoryTheory.Sites.Pullback` for the pullback of sheaves.
-/

@[expose] public section

universe v u'

open CategoryTheory Limits Opposite

noncomputable section

namespace CategoryTheory

section Over

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v} A] (W : C)
  [HasWeakSheafify J A] [HasWeakSheafify (J.over W) A]
  [∀ P : (Over W)ᵒᵖ ⥤ A, (Over.forget W).op.HasPointwiseRightKanExtension P]

/-- The constant sheaf functor commutes with localization of the site at an object:
the restriction of the constant sheaf at `a : A` to `J.over W` is the constant sheaf
at `a`. -/
def GrothendieckTopology.overPullbackConstantSheafIso :
    constantSheaf J A ⋙ J.overPullback A W ≅ constantSheaf (J.over W) A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
      ((Over.forget W).pushforwardContinuousSheafificationCompatibility A (J.over W) J).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ (Over.forget W).op)
      (presheafToSheaf (J.over W) A)

variable {J A} in
/-- The restriction of a constant sheaf to the site localized at an object is
constant. -/
lemma Sheaf.isConstant_over (F : Sheaf J A) [F.IsConstant J] :
    (F.over W).IsConstant (J.over W) := by
  obtain ⟨a, ⟨e⟩⟩ := F.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((J.overPullback A W).mapIso e.symm ≪≫ (J.overPullbackConstantSheafIso A W).app a)

end Over

section Pullback

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
  (A : Type u') [Category.{v} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]

/-- Sections of the pushforward of a sheaf along `G` over an object `X` are sections of
the sheaf over `G.obj X`. -/
def Functor.sheafPushforwardContinuousCompSheafSectionsObjIso (X : Cᵒᵖ) :
    G.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj X ≅
      (sheafSections K A).obj (G.op.obj X) :=
  NatIso.ofComponents (fun F ↦ Iso.refl _)

variable [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The constant sheaf functor commutes with the pullback of sheaves along a continuous
functor of sites which preserves a terminal object: the pullback of the constant sheaf
at `a : A` is the constant sheaf at `a`. -/
def Functor.constantSheafsheafPullbackIso {T : C} (hT : IsTerminal T)
    (hGT : IsTerminal (G.obj T)) :
    constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A :=
  (((constantSheafAdj J A hT).comp (G.sheafAdjunctionContinuous A J K)).ofNatIsoRight
    (G.sheafPushforwardContinuousCompSheafSectionsObjIso A J K (op T))).leftAdjointUniq
    (constantSheafAdj K A hGT)

variable {A J K} in
/-- The pullback of a constant sheaf along a continuous functor of sites which preserves
a terminal object is constant. -/
lemma Sheaf.isConstant_sheafPullback {T : C} (hT : IsTerminal T)
    (hGT : IsTerminal (G.obj T)) (F : Sheaf J A) [F.IsConstant J] :
    ((G.sheafPullback A J K).obj F).IsConstant K := by
  obtain ⟨a, ⟨e⟩⟩ := F.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((G.sheafPullback A J K).mapIso e.symm ≪≫
      (G.constantSheafsheafPullbackIso A J K hT hGT).app a)

end Pullback

end CategoryTheory

namespace CategoryTheory

/-- **Morphisms out of a constant sheaf.** On a site with a terminal object `T`, for an object
`E` of the coefficient category and a sheaf `F`, the map sending `φ : E̲ ⟶ F` to
`c_E ≫ φ_T : E ⟶ F(T)`, where `c_E : E ⟶ E̲(T)` is the unit of `constantSheafAdj`, is a
bijection: the constant sheaf functor is left adjoint to the global sections functor.
(blueprint: `situation-conventions`) -/
theorem bijective_constantSheafAdj_unit_comp {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (D : Type*) [Category* D] [HasWeakSheafify J D] {T : C}
    (hT : Limits.IsTerminal T) (E : D) (F : Sheaf J D) :
    Function.Bijective fun φ : (constantSheaf J D).obj E ⟶ F ↦
      (constantSheafAdj J D hT).unit.app E ≫ φ.hom.app (Opposite.op T) :=
  ((constantSheafAdj J D hT).homEquiv E F).bijective


end CategoryTheory
