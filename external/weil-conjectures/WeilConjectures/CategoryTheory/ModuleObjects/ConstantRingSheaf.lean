/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!
# Module objects over a constant ring sheaf are sheaves of modules

Let `(C, J)` be an essentially small site and `T` a ring. The constant ring sheaf `T`, the
sheafification `L(T)` of the constant ring presheaf `T`, is a ring object of the category
`Sheaf J Ab` of abelian sheaves, with the sheafified tensor product
(`CategoryTheory.Sheaf.constRingSheaf`). This file proves that module objects over it are the
sheaves of `T`-modules (`CategoryTheory.Sheaf.modConstRingSheafEquivalence`).

The proof is formal. Sheafification `L ⊣ i` is a monoidal adjunction, so it lifts to module
objects (`Adjunction.mapModAdjunction`): an `L(T)`-module `N` gives the `T`-module object `i N`,
with `T` acting through the unit `T ⟶ i L(T)` (`CategoryTheory.Sheaf.modToPresheafMod`), and
this functor is fully faithful since the counit of `L ⊣ i` is invertible. Its essential image
consists of the module objects whose underlying presheaf is a sheaf: for such an `M` the unit
`M ⟶ i L M` is invertible. Composing with the equivalence between module objects over the
constant ring presheaf and presheaves of `T`-modules
(`CategoryTheory.Presheaf.modConstRingEquivalence`), which keeps the underlying abelian
presheaf, gives the equivalence.

## Main definitions

* `CategoryTheory.Sheaf.modToSheafModule`: the sheaf of `T`-modules underlying a module object
  over the constant ring sheaf `T`; its underlying abelian sheaf is that of the module object.
* `CategoryTheory.Sheaf.modConstRingSheafEquivalence`: the equivalence
  `Mod (Sheaf J Ab) L(T) ≌ Sheaf J (ModuleCat T)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Opposite Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (T : Type (u + 1)) [Ring T]

/-- The constant ring sheaf `T`, the sheafification of the constant ring presheaf `T`, as a ring
object of abelian sheaves. -/
noncomputable abbrev constRingSheaf : Sheaf J Ab.{u + 1} :=
  (presheafToSheaf J Ab.{u + 1}).obj (Presheaf.constRingObj (C := C) T)

/-- The constant ring sheaf of a commutative ring is a commutative ring object, sheafification
being braided. -/
instance isCommMonObj_constRingSheaf (T : Type (u + 1)) [CommRing T] :
    IsCommMonObj (constRingSheaf J T) :=
  Functor.isCommMonObj_obj (F := presheafToSheaf J Ab.{u + 1})

/-- The underlying presheaf of a module object over the constant ring sheaf `T`, as a module
object over the constant ring presheaf `T`, acting through the sheafification unit. -/
noncomputable def modToPresheafMod :
    Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T) ⥤
      Mod (Cᵒᵖ ⥤ Ab.{u + 1}) (Presheaf.constRingObj (C := C) T) :=
  (sheafToPresheaf J Ab.{u + 1}).mapMod _ ⋙
    Mod.comap ((sheafificationAdjunction J Ab.{u + 1}).unitAlgHom _)

/-- Sheafification of module objects is left adjoint to `modToPresheafMod`. -/
noncomputable def sheafifyModAdjunction :
    (presheafToSheaf J Ab.{u + 1}).mapMod (Presheaf.constRingObj (C := C) T) ⊣
      modToPresheafMod J T :=
  (sheafificationAdjunction J Ab.{u + 1}).mapModAdjunction _

instance isIso_sheafifyModAdjunction_counit : IsIso (sheafifyModAdjunction J T).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  have : IsIso ((Mod.forget _).map ((sheafifyModAdjunction J T).counit.app N)) := by
    rw [Mod.forget_map, sheafifyModAdjunction, Adjunction.mapModAdjunction_counit_app_hom]
    exact isIso_sheafificationAdjunction_counit N.X
  exact isIso_of_reflects_iso _ (Mod.forget _)

/-- `modToPresheafMod` is fully faithful. -/
noncomputable def fullyFaithfulModToPresheafMod : (modToPresheafMod J T).FullyFaithful :=
  (sheafifyModAdjunction J T).fullyFaithfulROfIsIsoCounit

/-- A module object over the constant ring sheaf `T` as a sheaf of `T`-modules. -/
noncomputable def modToSheafModule :
    Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T) ⥤ Sheaf J (ModuleCat.{u + 1} T) where
  obj M := ⟨(Presheaf.modToModule T).obj ((modToPresheafMod J T).obj M),
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1}) M.X.property⟩
  map f := ⟨(Presheaf.modToModule T).map ((modToPresheafMod J T).map f)⟩

/-- `modToSheafModule` is fully faithful. -/
noncomputable def fullyFaithfulModToSheafModule : (modToSheafModule J T).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := sheafToPresheaf J (ModuleCat.{u + 1} T))
    ((fullyFaithfulModToPresheafMod J T).comp
      (Presheaf.modConstRingEquivalence C T).fullyFaithfulFunctor)

instance : (modToSheafModule J T).Full := (fullyFaithfulModToSheafModule J T).full

instance : (modToSheafModule J T).Faithful := (fullyFaithfulModToSheafModule J T).faithful

instance : (modToSheafModule J T).EssSurj where
  mem_essImage N := by
    let Q := (Presheaf.moduleToMod T).obj N.obj
    have : IsIso ((sheafifyModAdjunction J T).unit.app Q) := by
      have : IsIso ((Mod.forget _).map ((sheafifyModAdjunction J T).unit.app Q)) := by
        rw [Mod.forget_map, sheafifyModAdjunction, Adjunction.mapModAdjunction_unit_app_hom,
          sheafificationAdjunction_unit_app]
        exact isIso_toSheafify J ((sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj
          N).property
      exact isIso_of_reflects_iso _ (Mod.forget _)
    exact ⟨((presheafToSheaf J Ab.{u + 1}).mapMod _).obj Q,
      ⟨(fullyFaithfulSheafToPresheaf J _).preimageIso
        ((Presheaf.modToModule T).mapIso (asIso ((sheafifyModAdjunction J T).unit.app Q)).symm ≪≫
          Presheaf.counitIsoApp N.obj)⟩⟩

instance : (modToSheafModule J T).IsEquivalence where

/-- Module objects over the constant ring sheaf `T` in abelian sheaves are the sheaves of
`T`-modules. -/
noncomputable def modConstRingSheafEquivalence :
    Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T) ≌ Sheaf J (ModuleCat.{u + 1} T) :=
  (modToSheafModule J T).asEquivalence

/-- The abelian sheaf underlying the sheaf of `T`-modules of a module object is its underlying
abelian sheaf. -/
lemma modToSheafModule_comp_sheafCompose :
    modToSheafModule J T ⋙ sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1}) =
      Mod.forget (constRingSheaf J T) :=
  rfl


end CategoryTheory.Sheaf
