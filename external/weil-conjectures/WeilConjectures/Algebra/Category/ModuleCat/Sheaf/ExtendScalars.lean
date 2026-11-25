/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.CategoryTheory.Sites.ReductionFlat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Extension of scalars for sheaves of modules over a constant ring

Let `S` be an algebra over a commutative ring `R` and `J` a Grothendieck topology. Extension of
scalars `F ↦ S ⊗_R F` of sheaves of `R`-modules is the sheafification
`Sheaf.composeAndSheafify J (ModuleCat.extendScalars (algebraMap R S))` of the objectwise extension
of scalars. Restricting the scalars of `S ⊗_R F` back to `R` gives the tensor product `F ⊗ S_X`
with the constant sheaf
(`CategoryTheory.Sheaf.extendScalarsCompRestrictScalarsIso`).

This generalises the reduction `CategoryTheory.Sheaf.quotSMulTop` modulo an ideal, the case
`S = R ⧸ I`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} S))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} S)]

/-- **Restricting the scalars of the extension gives the tensor product with `S`.** For a
sheaf `F` of `R`-modules, the extension `S ⊗_R F` with scalars restricted back to `R` is
`F ⊗ S_X`, naturally in `F`. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap R S)) ⋙
        restrictScalars J (algebraMap R S) ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R S)) :=
  haveI : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
    preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  haveI : HasWeakSheafify J (ModuleCat.{u + 1} S) := inferInstance
  haveI : HasWeakSheafify J (ModuleCat.{u + 1} R) := inferInstance
  let P := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (algebraMap R S))
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let ι := Sheaf.restrictScalars J (algebraMap R S)
  let X := (Functor.const Cᵒᵖ).obj (ModuleCat.of R S)
  Functor.associator P (W ⋙ a') ι ≪≫
    Functor.isoWhiskerLeft P (Functor.associator W a' ι) ≪≫
    Functor.isoWhiskerLeft P (Functor.isoWhiskerLeft W
      (sheafComposeNatIso J (ModuleCat.restrictScalars (algebraMap R S))
        (sheafificationAdjunction J (ModuleCat.{u + 1} S))
        (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
    Functor.isoWhiskerLeft P (Functor.associator W _ a).symm ≪≫
    Functor.isoWhiskerLeft P (Functor.isoWhiskerRight
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight _ _ _).mapIso
          (ModuleCat.extendScalarsCompRestrictScalarsIso' R S) ≪≫
        whiskeringRightTensorRightIso _) a) ≪≫
    Functor.isoWhiskerLeft P (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
    (Functor.associator P a (tensorRight (a.obj X))).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
      (tensorRight (a.obj X)) ≪≫
    Functor.leftUnitor _

end CategoryTheory.Sheaf
