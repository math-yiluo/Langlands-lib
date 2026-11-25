/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.SixFunctors.ProEtale.Adic.FreeWeilCoefficients

import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Monoidality of forgetting ambient scalars

## References

* Stacks Tags 03EK and 07A4, relative tensor and extension of scalars
-/

@[expose] public section
set_option autoImplicit false
universe u
open scoped CategoryTheory.Obj
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale

private theorem monoidalRightAdjointOfEquivalence
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] [G.IsEquivalence] (a : F ⊣ G) :
    Nonempty G.Monoidal := by
  have : F.IsEquivalence := a.isEquivalence_left_of_isEquivalence_right
  let : F.asEquivalence.functor.Monoidal := inferInstanceAs F.Monoidal
  let : F.asEquivalence.inverse.Monoidal := F.asEquivalence.inverseMonoidal
  exact ⟨Functor.Monoidal.transport (F.asEquivalence.toAdjunction.rightAdjointUniq a)⟩

/-- Forgetting ambient scalars admits a strong monoidal structure for relative tensor.
This is entirely underived and involves no choice of closed models. -/
theorem nativeScalarForgetting_monoidal (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    Nonempty (AdicSheaf.forgetAb l Y).Monoidal := by
  classical
  let F := Sheaf.extendScalarsAb (Scheme.ProEt.topology Y)
    (ULift.{u + 1} (PadicAlgCl l))
  let G := weilCoefficientsForgetAb l Y
  let a : F ⊣ G := Sheaf.extendScalarsAbAdjunction (Scheme.ProEt.topology Y)
    (ULift.{u + 1} (PadicAlgCl l))
  have : F.IsLeftAdjoint := a.isLeftAdjoint
  let B := adicConstantSheaf l Y
  let A := G.obj B
  let φ := a.counitAlgHom B
  obtain ⟨m, _hm⟩ := Mod.exists_extendScalarsMonoidal φ
  let : (Mod.extendScalars φ).Monoidal := m
  let : (F.mapMod A).Monoidal := Functor.monoidal_mapMod F
  let L := F.mapMod A ⋙ Mod.extendScalars φ
  let : L.Monoidal := inferInstanceAs (F.mapMod A ⋙ Mod.extendScalars φ).Monoidal
  let r : Mod.comap φ ⋙ (G.mapMod (F.obj A) ⋙ Mod.comap (a.unitAlgHom A)) ≅
      AdicSheaf.forgetAb l Y :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapModComapIso φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Mod.comapComp _ _).symm ≪≫
        Mod.comapCongr (a.right_triangle_components B) ≪≫ Mod.comapId _)
  let b : L ⊣ AdicSheaf.forgetAb l Y :=
    ((a.mapModAdjunction A).comp (Mod.extendRestrictAdjunction φ)).ofNatIsoRight r
  have : (AdicSheaf.forgetAb l Y).IsEquivalence := nativeScalarForgetting_isEquivalence l Y
  exact monoidalRightAdjointOfEquivalence L (AdicSheaf.forgetAb l Y) b

end AlgebraicGeometry.ProEtale
