/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionEvaluation
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionCoherence
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleCofinalSupportEvaluation

/-! # Geometric realization of cofinal support

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a av b bv c cv d dv e ev g gv
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

attribute [local irreducible] WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings

section Pushforward
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    {L : GrothendieckTopology C} {F : A ⥤ B} {G : B ⥤ C}
    [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {R' : Sheaf L RingCat.{u}}

end Pushforward

section Comparison
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {E : Type e} [Category.{ev} E] {G : Type g} [Category.{gv} G]
    {Lx : A ⥤ C} {Rx : A ⥤ B} {Sx : B ⥤ C}
    {Ly : D ⥤ G} {Ry : D ⥤ E} {Sy : E ⥤ G}
    {FB : C ⥤ G} {FD : B ⥤ E} {FS : A ⥤ D}
    (Fx : Lx ≅ Rx ⋙ Sx) (Fy : Ly ≅ Ry ⋙ Sy)
    (q : FD ⋙ Sy ≅ Sx ⋙ FB) (κ : Rx ⋙ FD ≅ FS ⋙ Ry)

private def supportComparison : Lx ⋙ FB ≅ FS ⋙ Ly :=
  Functor.isoWhiskerRight Fx FB ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Rx q.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight κ Sy ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft FS Fy.symm

end Comparison

private theorem level_jointly_reflects (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    JointlyReflectIsomorphisms (level W B) where
  isIso {M N} h hh := by
    have : IsIso
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map h) := by
      apply (NatTrans.isIso_iff_isIso_app _).2
      intro U
      have := hh U.unop.1
      have hs : IsIso (((level W B U.unop.1).map h).hom.app (op U.unop.2)) :=
        inferInstance
      have hb := (ConcreteCategory.isIso_iff_bijective
        (((level W B U.unop.1).map h).hom.app (op U.unop.2))).1 hs
      apply (ConcreteCategory.isIso_iff_bijective _).2
      change Function.Bijective (fun x ↦ h.val.app U x) at hb ⊢
      exact hb
    exact isIso_of_reflects_iso h
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

attribute [local irreducible] CofinalRepeatSupport.kappa

end AlgebraicGeometry.Etale.SystemProjection
