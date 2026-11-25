/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleScalar.ConstantModuleScalarCenter

/-! # Constant scalar multiplication under exact algebraic inverse image -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory.ConstantModuleScalar

private def constantScalar
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] [HasSheafify J (Type r)]
    [J.HasSheafCompose (forget CommRingCat.{r})]
    (B : CommRingCat.{r}) (b : B) :
    (constantSheaf J (Type r)).obj PUnit.{r + 1} ⟶
      (sheafCompose J (forget CommRingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj B) :=
  (constantSheaf J (Type r)).map (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b)) ≫
    (constantCommuteCompose J (forget CommRingCat.{r})).inv.app B

private theorem constantScalar_apply
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] [HasSheafify J (Type r)]
    [J.HasSheafCompose (forget CommRingCat.{r})]
    (B : CommRingCat.{r}) (b : B) (U : Cᵒᵖ)
    (t : ((constantSheaf J (Type r)).obj PUnit.{r + 1}).obj.obj U) :
    (constantScalar J B b).hom.app U t =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b := by
  let P := (Functor.const Cᵒᵖ).obj PUnit.{r + 1}
  let : IsIso (toSheafify J P) :=
    isIso_toSheafify J (Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)
  obtain ⟨x, hx⟩ := ((isIso_iff_bijective _).mp
    (inferInstance : IsIso ((toSheafify J P).app U))).2 t
  subst t
  have hn := congrArg (fun f ↦ f.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
      (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b))))
  change _ = ((constantSheaf J (Type r)).map
    (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b))).hom.app U
      ((toSheafify J P).app U x) at hn
  change ((constantCommuteCompose J (forget CommRingCat.{r})).inv.app
    B).hom.app U _ = _
  have hn' : ((constantSheaf J (Type r)).map
      (TypeCat.ofHom (fun _ : PUnit.{r + 1} ↦ b))).hom.app U
        ((toSheafify J P).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (B : Type r))).app U b := hn.symm
  apply Eq.trans (congrArg
    (fun z ↦ ((constantCommuteCompose J (forget CommRingCat.{r})).inv.app
      B).hom.app U z) hn')
  have hf := congrArg (fun f ↦ f.app U b)
    (sheafComposeIso_hom_fac J (forget CommRingCat.{r})
      ((Functor.const Cᵒᵖ).obj B))
  have hconst := toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ (forget CommRingCat.{r})).hom.app B)
  have hp := congrArg (fun f ↦ f.app U b) hconst
  dsimp at hp
  change ((sheafifyComposeIso J (forget CommRingCat.{r})
    ((Functor.const Cᵒᵖ).obj B)).hom.app U)
      ((((presheafToSheaf J (Type r)).map
        ((Functor.compConstIso Cᵒᵖ (forget CommRingCat.{r})).hom.app
          B)).hom.app U)
            ((toSheafify J ((Functor.const Cᵒᵖ).obj (B : Type r))).app U b)) = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget CommRingCat.{r})
    ((Functor.const Cᵒᵖ).obj B)).hom.app U) z) hp.symm).trans hf

private def toConstantUnit
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] [HasSheafify J (Type r)]
    [J.HasSheafCompose (forget CommRingCat.{r})]
    (T : Sheaf J (Type r)) : T ⟶ (constantSheaf J (Type r)).obj PUnit.{r + 1} where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun _ ↦
      (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{r + 1})).app U PUnit.unit)
      naturality := by
        intro U V f
        ext t
        exact congrArg (fun g ↦ g PUnit.unit)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{r + 1})).naturality f) }

end CategoryTheory.ConstantModuleScalar
