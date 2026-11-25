/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheafMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.TensorIso

/-!
# Module objects over a constant ring sheaf are sheaves of modules, compatibly with `⊗`

Let `(C, J)` be an essentially small site and `T` a commutative ring. The equivalence
`CategoryTheory.Sheaf.modToSheafModule` between module objects over the constant ring sheaf `T`
and sheaves of `T`-modules commutes with the tensor products, naturally in both variables
(`CategoryTheory.Sheaf.modToSheafModuleTensorIso`); no compatibility with the associators is
claimed.

The proof is formal. Let `P` be the sheafification of presheaves of `T`-modules through module
objects (`CategoryTheory.Sheaf.sheafifyModule`), `G := modToSheafModule` and `Q` the underlying
presheaf of `T`-modules of a module object. Then
* `P` commutes with `⊗`, as the composite of `Presheaf.moduleToMod` (see
  `Presheaf.moduleToModTensorIso`) and the strong monoidal functor `mapMod` of sheafification;
* `P ⋙ G` is the sheafification of presheaves of `T`-modules (both are left adjoint to the
  forgetful functor, `CategoryTheory.Sheaf.sheafifyModuleCompIso`), which is strong monoidal;
* `Q ⋙ P ≅ 𝟭` (`CategoryTheory.Sheaf.sheafifyModuleUnderlyingIso`), the counit of the
  sheafification of module objects being invertible.
The tensor isomorphism of `G` is then obtained by `Functor.TensorIso.ofCompIso`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Opposite Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (T : Type (u + 1)) [CommRing T]

/-- Sheafification of presheaves of `T`-modules, through module objects: a presheaf of
`T`-modules, as a module object over the constant ring presheaf, sheafified to a module object
over the constant ring sheaf. -/
noncomputable abbrev sheafifyModule :
    (Cᵒᵖ ⥤ ModuleCat.{u + 1} T) ⥤ Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T) :=
  Presheaf.moduleToMod T ⋙ (presheafToSheaf J Ab.{u + 1}).mapMod (Presheaf.constRingObj T)

/-- `sheafifyModule` is left adjoint to the underlying presheaf of `T`-modules. -/
noncomputable def sheafifyModuleAdjunction :
    sheafifyModule J T ⊣ modToPresheafMod J T ⋙ Presheaf.modToModule T :=
  (Presheaf.modConstRingEquivalence C T).symm.toAdjunction.comp (sheafifyModAdjunction J T)

/-- The sheaf of `T`-modules of the sheafification, through module objects, of a presheaf of
`T`-modules is its sheafification. -/
noncomputable def sheafifyModuleCompIso :
    sheafifyModule J T ⋙ modToSheafModule J T ≅ presheafToSheaf J (ModuleCat.{u + 1} T) :=
  ((sheafifyModuleAdjunction J T).comp (modConstRingSheafEquivalence J T).toAdjunction
    |>.ofNatIsoRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (modConstRingSheafEquivalence J T).counitIso
        (sheafToPresheaf J (ModuleCat.{u + 1} T)) ≪≫ Functor.leftUnitor _)).leftAdjointUniq
    (sheafificationAdjunction J (ModuleCat.{u + 1} T))

/-- A module object over the constant ring sheaf is the sheafification of its underlying
presheaf of `T`-modules. -/
noncomputable def sheafifyModuleUnderlyingIso :
    (modToSheafModule J T ⋙ sheafToPresheaf J (ModuleCat.{u + 1} T)) ⋙ sheafifyModule J T ≅
      𝟭 _ :=
  Functor.associator (modToPresheafMod J T) (Presheaf.modToModule T) (sheafifyModule J T) ≪≫
    Functor.isoWhiskerLeft (modToPresheafMod J T)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Presheaf.modConstRingEquivalence C T).unitIso.symm _ ≪≫
        Functor.leftUnitor _) ≪≫
    asIso (sheafifyModAdjunction J T).counit

/-- The equivalence `modToSheafModule` between module objects over the constant ring sheaf `T`
and sheaves of `T`-modules commutes with the tensor products:
`(M ⊗_T N)^♯ ≅ M^♯ ⊗ N^♯`, naturally in `M` and `N`. -/
noncomputable def modToSheafModuleTensorIso :
    (Functor.postcompose₂.obj (modToSheafModule J T)).obj
        (curriedTensor (Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T))) ≅
      (((Functor.whiskeringLeft₂ _).obj (modToSheafModule J T)).obj (modToSheafModule J T)).obj
        (curriedTensor (Sheaf J (ModuleCat.{u + 1} T))) :=
  Functor.TensorIso.ofCompIso (sheafifyModuleUnderlyingIso J T)
    (Functor.TensorIso.comp (Presheaf.moduleToModTensorIso (C := C) T)
      (Functor.Monoidal.tensorIso ((presheafToSheaf J Ab.{u + 1}).mapMod _)))
    (Functor.TensorIso.ofIso
      (Functor.Monoidal.tensorIso (presheafToSheaf J (ModuleCat.{u + 1} T)))
      (sheafifyModuleCompIso J T).symm)

end CategoryTheory.Sheaf
