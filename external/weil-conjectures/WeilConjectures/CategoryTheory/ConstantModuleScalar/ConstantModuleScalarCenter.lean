/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations
public import Mathlib.CategoryTheory.Center.Localization

/-! # Constant scalar endomorphisms and their exact localization -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v r w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory.ConstantModuleScalar

/-- Multiplication by a constant section, as an element of the module category's center.
Source: Stacks 03CZ, finite-basis calculation
(blueprint: def-pur-constant-module-scalar-center). -/
def ordinary {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (B : CommRingCat.{r}) (b : B) : CatCenter (modules (constantRing J B)) := .of {
  app M := { val :=
    { app := fun V ↦ ModuleCat.ofHom
        (LinearMap.lsmul _ _ ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V b))
      naturality := by
        intro V W f
        ext x
        symm
        refine (M.val.map_smul f _ x).trans ?_
        congr 1
        exact CategoryTheory.congr_fun
          ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).naturality f) b |>.symm } }
  naturality {M N} f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    ext x
    exact ((f.val.app V).hom.map_smul _ x).symm
}

/-- The termwise scalar endomorphism on unbounded cochain complexes.
Source: Stacks 07A6 (blueprint: def-pur-constant-module-scalar-center). -/
def cochain {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (B : CommRingCat.{r}) (b : B) :
    CatCenter (CochainComplex (modules (constantRing J B)) ℤ) := .of {
  app K := { f n := (ordinary J B b).app (K.X n)
             comm' i j _ := ((ordinary J B b).naturality (K.d i j)).symm }
  naturality {K L} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (ordinary J B b).naturality (f.f n)
}

/-- Scalar multiplication on the ordinary unbounded derived category, obtained by
localizing its termwise endomorphism. No representatives are chosen.
Source: Stacks 07A6 (blueprint: def-pur-constant-module-scalar-center). -/
def derived {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (B : CommRingCat.{r}) [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (modules (constantRing J B))]
    (b : B) : CatCenter (DerivedCategory (modules (constantRing J B))) :=
  (cochain J B b).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))

end CategoryTheory.ConstantModuleScalar
