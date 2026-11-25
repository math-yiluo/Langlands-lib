/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
public import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

set_option linter.privateModule false

/-! # Computing derived pullback on K-flat tensor representatives -/

@[expose] public section
set_option autoImplicit false
universe s h w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.CanonicalTensorPullbackOfUniverses
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

private noncomputable abbrev moduleUnderlying
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max s h})

private theorem moduleUnderlying_finiteLimits
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h}) : PreservesFiniteLimits (moduleUnderlying R) := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max s h})
  have : PreservesFiniteLimits (V ⋙ sheafToPresheaf J (Type (max s h))) :=
    show PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{max s h} ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{max s h})) from
        comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits V :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type (max s h)))
  exact comp_preservesFiniteLimits _ _

private theorem algebraicInverseImage_finiteLimits
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {RI : Sheaf JD CommRingCat.{max s h}}
    (L : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h))) [PreservesFiniteLimits L]
    (I : AlgebraicInverseImage L R RI) : PreservesFiniteLimits I.modules := by
  have := moduleUnderlying_finiteLimits R
  have := moduleUnderlying_finiteLimits RI
  have : PreservesFiniteLimits (moduleUnderlying R ⋙ L) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (I.modules ⋙ moduleUnderlying RI) :=
    preservesFiniteLimits_of_natIso I.moduleUnderlying.symm
  exact preservesFiniteLimits_of_reflects_of_preserves I.modules (moduleUnderlying RI)

private noncomputable def scalarExtensionPresheaf
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{max s h}} (c : R ⟶ S) :
    SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      PresheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj where
  obj M := changeOfRingsPresheaf.{h, s, max s h} c M
  map {M N} f :=
    { app := fun U ↦ (ModuleCat.extendScalars (c.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality.{h, s, max s h} c M f }
  map_id M := by
    ext U : 1
    simp
    rfl
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (c.hom.app U).hom).map_comp _ _

private theorem scalarExtensionPresheaf_additive
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{max s h}} (c : R ⟶ S) :
    (scalarExtensionPresheaf c).Additive where
  map_add {M N} f g := by
    ext U : 1
    have : (ModuleCat.extendScalars (c.hom.app U).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (c.hom.app U).hom).left_adjoint_additive
    simpa only [scalarExtensionPresheaf, add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (c.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)

private noncomputable def scalarExtension
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{max s h}} (c : R ⟶ S) :
    SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) :=
  scalarExtensionPresheaf c ⋙ PresheafOfModules.sheafification.{max s h}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)

private theorem scalarExtension_additive
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{max s h}} (c : R ⟶ S) :
    (scalarExtension c).Additive := by
  have hsheaf : (PresheafOfModules.sheafification.{max s h}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  have := scalarExtensionPresheaf_additive c
  dsimp only [scalarExtension]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionPresheafIdIso
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h})
    (M : SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M.val ≅ (scalarExtensionPresheaf (𝟙 R)).obj M := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId (R.obj.obj U)).app (M.val.obj U)).symm) ?_
  intro U V i
  ext m
  change (ModuleCat.extendScalarsId (R.obj.obj V)).inv.app (M.val.obj V)
      (M.val.map i m) =
    changeOfRingsMap (𝟙 R) M i
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [changeOfRingsMap] using
    (Classical.choose_spec (exists_changeOfRingsMap (𝟙 R) M i)
      (1 : R.obj.obj U) m).symm

private noncomputable def scalarExtensionIdIsoApp
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h})
    (M : SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (scalarExtension (𝟙 R)).obj M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso
      (scalarExtensionPresheafIdIso R M).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionIdIso
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h}) : scalarExtension (𝟙 R) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (scalarExtensionIdIsoApp R) ?_
  intro M N a
  let F := PresheafOfModules.sheafification.{max s h}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let ψ := (scalarExtensionPresheaf (𝟙 R)).map a
  have hp : (scalarExtensionPresheafIdIso R M).hom ≫ ψ =
      a.val ≫ (scalarExtensionPresheafIdIso R N).hom := by
    ext U m
    change (ModuleCat.extendScalars (RingHom.id (R.obj.obj U))).map (a.val.app U)
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m) =
        (ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (N.val.obj U) (a.val.app U m)
    exact ConcreteCategory.congr_hom ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.naturality
      (a.val.app U)) m
  have hp' : (scalarExtensionPresheafIdIso R M).inv ≫ a.val =
      ψ ≫ (scalarExtensionPresheafIdIso R N).inv := by
    rw [← cancel_epi (scalarExtensionPresheafIdIso R M).hom]
    simp only [← Category.assoc, hp]
    simp
  symm
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M ≫ a =
    F.map ψ ≫ F.map (scalarExtensionPresheafIdIso R N).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app N
  rw [← (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit_naturality a]
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫ F.map a.val ≫ _ = _
  rw [← F.map_comp_assoc, hp', F.map_comp_assoc]

set_option synthInstance.maxSize 256 in
open MonoidalCategory in
private theorem isKFlat_of_iso
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max s h}}
    {P Q : CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (e : P ≅ Q) (hP : P.IsKFlatTensor) : Q.IsKFlatTensor := by
  let := monoidalCategory R
  intro A hA n
  let F := (MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e' : CochainComplex.mapBifunctor A P (curriedTensor _) ≅
      CochainComplex.mapBifunctor A Q (curriedTensor _) :=
    HomologicalComplex₂.total.mapIso ((F.obj A).mapIso e) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hP A hA n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e').symm |>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).2

private theorem isKFlat_inverseImage
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {RI : Sheaf JD CommRingCat.{max s h}}
    (L : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (V : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h))) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (I : AlgebraicInverseImage L R RI) [I.modules.Additive]
    (P : CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hP : P.IsKFlatTensor) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatTensor
      ((I.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have := algebraicInverseImage_finiteLimits L I
  have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
  have := scalarExtension_additive (𝟙 RI)
  let U := I.modules ⋙ scalarExtension (𝟙 RI)
  have hobj (M) : U.obj M = changeOfRings (𝟙 RI) (I.modules.obj M) := rfl
  have hmap {M N} (a : M ⟶ N) : U.map a = eqToHom (hobj M) ≫
      changeOfRingsHom (𝟙 RI) (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hk := (isKFlat_ringedToposPullback L V adj I (𝟙 RI) U hobj hmap P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP)
      hf).1
  let e : U ≅ I.modules :=
    Functor.isoWhiskerLeft I.modules (scalarExtensionIdIso RI) ≪≫ I.modules.rightUnitor
  exact isKFlat_of_iso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk)

end SheafOfModules.CanonicalTensorPullbackOfUniverses
