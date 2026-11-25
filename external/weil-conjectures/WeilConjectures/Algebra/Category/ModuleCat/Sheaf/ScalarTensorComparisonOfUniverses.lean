/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-!
# Scalar-extension tensor comparison in independent universes

Source: Stacks Project, Modules on Sites, Tag 05V4.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v r m
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasWeakSheafify J AddCommGrpCat.{max r m}]
  {R S : Sheaf J CommRingCat.{r}} (c : R ⟶ S)
  (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  (N : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))

private noncomputable def rawScalarTensorIso :
    (siteTensorPresheaf
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map c)).obj N).val
      M.val).presheaf ≅
    (siteTensorPresheaf N.val (changeOfRingsPresheafOfUniverses c M)).presheaf :=
  NatIso.ofComponents (fun U ↦ by
    letI := (c.hom.app U).hom.toAlgebra
    letI : Module (R.obj.obj U) (N.val.obj U) :=
      Module.compHom (N.val.obj U) (c.hom.app U).hom
    letI : IsScalarTower (R.obj.obj U) (S.obj.obj U) (N.val.obj U) :=
      IsScalarTower.of_compHom _ _ _
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (R.obj.obj U) (S.obj.obj U) (S.obj.obj U)
      (N.val.obj U) (M.val.obj U)).symm.toAddEquiv.toAddCommGrpIso) (by
    intro U V i
    apply AddCommGrpCat.hom_ext
    ext z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul n x =>
      let : Module (R.obj.obj V) (S.obj.obj V) :=
        Module.compHom (S.obj.obj V) (c.hom.app V).hom
      change TensorProduct.tmul (S.obj.obj V) (M := N.val.obj V)
        (N := (ModuleCat.extendScalars (c.hom.app V).hom).obj (M.val.obj V))
        (N.val.map i n)
        (TensorProduct.tmul (R.obj.obj V) (M := S.obj.obj V) (N := M.val.obj V)
          1 (M.val.map i x)) =
        TensorProduct.tmul (S.obj.obj V) (M := N.val.obj V)
          (N := (ModuleCat.extendScalars (c.hom.app V).hom).obj (M.val.obj V))
          (N.val.map i n) (changeOfRingsMapOfUniverses c M i
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))
      rw [changeOfRingsMap_tmulOfUniverses, map_one])

private noncomputable def tensorSwapIso {A : Cᵒᵖ ⥤ CommRingCat.{r}}
    (P Q : PresheafOfModules.{max r m} (A ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorPresheaf P Q ≅ siteTensorPresheaf Q P :=
  PresheafOfModules.isoMk
    (fun U ↦ (TensorProduct.comm (A.obj U) (P.obj U) (Q.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      rfl)

private noncomputable def tensorSheafificationUnit {A : Sheaf J CommRingCat.{r}}
    (P : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).unit.app P

private instance tensorSheafificationUnit_locallyInjective {A : Sheaf J CommRingCat.{r}}
    (P : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallyInjective J (tensorSheafificationUnit (J := J) P) := by
  change PresheafOfModules.IsLocallyInjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

private instance tensorSheafificationUnit_locallySurjective {A : Sheaf J CommRingCat.{r}}
    (P : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallySurjective J (tensorSheafificationUnit (J := J) P) := by
  change PresheafOfModules.IsLocallySurjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance


private noncomputable def tensorSecondMap {A : Cᵒᵖ ⥤ CommRingCat.{r}}
    {P Q : PresheafOfModules.{max r m} (A ⋙ forget₂ CommRingCat RingCat)}
    (f : P ⟶ Q) (N : PresheafOfModules.{max r m} (A ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorPresheaf N P ⟶ siteTensorPresheaf N Q :=
  (tensorSwapIso N P).hom ≫ siteTensorHom f N ≫ (tensorSwapIso Q N).hom

private theorem sheafification_tensorSecondUnit_isIso {A : Sheaf J CommRingCat.{r}}
    (P N : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    IsIso ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).map
      (tensorSecondMap (tensorSheafificationUnit (J := J) P) N)) := by
  have : IsIso ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).map
      (siteTensorHom (tensorSheafificationUnit (J := J) P) N)) :=
    PresheafOfModules.sheafification_tensorHom_isIso (J := J)
    (f := tensorSheafificationUnit (J := J) P) (N := N)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).property
  dsimp only [tensorSecondMap]
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

private noncomputable def sheafifiedUnitTensorIso {A : Sheaf J CommRingCat.{r}}
    (P N : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    (presheafToSheaf J AddCommGrpCat).obj (siteTensorPresheaf N P).presheaf ≅
      (presheafToSheaf J AddCommGrpCat).obj
        (siteTensorPresheaf N ((PresheafOfModules.sheafification
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).obj P).val).presheaf :=
  letI := sheafification_tensorSecondUnit_isIso (J := J) P N
  (toSheaf _).mapIso (asIso ((PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).map
    (tensorSecondMap (tensorSheafificationUnit (J := J) P) N)))

private theorem sheafifiedUnitTensorIso_hom {A : Sheaf J CommRingCat.{r}}
    (P N : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    (sheafifiedUnitTensorIso (J := J) P N).hom =
      (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf _).map
          (tensorSecondMap (tensorSheafificationUnit (J := J) P) N)) := rfl


omit N in
private noncomputable def rawTensorComparison :
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map c) ⋙
      forget _ ⋙ siteTensorRight M.val ⋙ PresheafOfModules.toPresheaf _ ⟶
    forget _ ⋙ siteTensorRight (changeOfRingsOfUniverses c M).val ⋙
      PresheafOfModules.toPresheaf _ where
  app N := (rawScalarTensorIso c M N).hom ≫
    (PresheafOfModules.toPresheaf _).map
      (tensorSecondMap
        (tensorSheafificationUnit (J := J) (changeOfRingsPresheafOfUniverses c M)) N.val)
  naturality {N N'} f := by
    ext U z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul n x => rfl

omit N in
/-- Scalar-extension tensor associativity on underlying abelian sheaves.
Source: Stacks Project, Modules on Sites, Tag 05V4 (lemma-flat-change-of-rings)
(auxiliary; not a blueprint node).
Proof: before sheafification the comparison is `n ⊗ m ↦ n ⊗ (1 ⊗ m)`, with
inverse `n ⊗ (s ⊗ m) ↦ (s • n) ⊗ m`. The standard base-change tensor equivalence
supplies this isomorphism sectionwise, and its pure-tensor formula proves naturality.
Next apply the sheafification unit of the scalar-extension presheaf in the second
factor. This unit is locally bijective; tensor descent shows its sheafified tensor map
is invertible. Compose these isomorphisms. They are natural in the module `N`, because
both composites send `n ⊗ m` to `f(n) ⊗ η(1 ⊗ m)` before sheafification. -/
theorem nonempty_scalarTensorComparisonOfUniverses :
    Nonempty (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map c) ⋙
      siteSheafTensorRight M ⋙
        toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ≅
      siteSheafTensorRight (changeOfRingsOfUniverses c M) ⋙
        toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) := by
  let a := presheafToSheaf J AddCommGrpCat.{max r m}
  let f := Functor.whiskerRight (rawTensorComparison c M) a
  have h : ∀ N, IsIso (f.app N) := by
    intro N
    change IsIso (a.map ((rawTensorComparison c M).app N))
    dsimp only [rawTensorComparison]
    rw [Functor.map_comp]
    rw [← a.mapIso_hom (rawScalarTensorIso c M N)]
    erw [← sheafifiedUnitTensorIso_hom (J := J) (A := S)
      (changeOfRingsPresheafOfUniverses c M) N.val]
    infer_instance
  have : IsIso f := NatIso.isIso_of_isIso_app f
  exact ⟨asIso f⟩

end SheafOfModules
