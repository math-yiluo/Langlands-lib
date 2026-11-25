/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Composition of intrinsic rational scalar extensions

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1469; current main snapshot sec-proper-base-change/sk-thm-properbasechange,
order 1828 (blueprint: lem-weil-scalar-extension-composition).

The ordinary balanced tensor associator and unit are reused from the legacy module.
Their quotient-completion normalization is transported to the current intrinsic integral
subcategory and then to its raw Hom scalar localization. No identification with the legacy
integral constructibility predicate is assumed.

## Main statements

- `sfRationalScalarComp`: canonical composition on the currently recorded rational stages.
- `sfRationalScalarUnit`: the normalized identity-extension comparison.
- `sfRationalScalar_coherence`: both unit equations and the pentagon.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe r u v

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralScalarExtension integralOrdinaryScalar

section OrdinaryCoherence
attribute [local irreducible] integralCompletedScalarMap integralOrdinaryTensorSection
  integralOrdinaryScalarComp integralOrdinaryScalarUnit
section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
variable
  (F : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  (h : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
  (hm : ∀ {N N' : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : N ⟶ N'), F.map f = eqToHom (h N) ≫
    SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (h N').symm)
private noncomputable def tensorSection
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :=
  (eqToHom (h N).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
private theorem tensorSection_ext
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (f g : F.obj N ⟶ T)
    (he : ∀ (U : Cᵒᵖ) (x : N.val.obj U),
      f.val.app U (tensorSection φ F h N U 1 x) =
        g.val.app U (tensorSection φ F h N U 1 x)) : f = g := by
  let e := eqToIso (h N)
  apply (cancel_epi e.inv).mp
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  ext1 U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact he U x

include hm in
private theorem tensorSection_map
    {N N' : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : N ⟶ N') (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : N.val.obj U) :
    (F.map f).val.app U (tensorSection φ F h N U s x) =
      tensorSection φ F h N' U s (f.val.app U x) := by
  let a : SheafOfModules.changeOfRingsPresheaf φ N ⟶
      SheafOfModules.changeOfRingsPresheaf φ N' :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ N f }
  have hn := congrArg (fun t ↦ t.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
    (CategoryTheory.toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map a))
  rw [hm]
  change (eqToHom (h N').symm).val.app U
    ((SheafOfModules.changeOfRingsHom φ N f).val.app U
      ((eqToHom (h N)).val.app U (tensorSection φ F h N U s x))) = _
  dsimp only [tensorSection]
  have hc {A B : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
      (e : A = B) (z : B.val.obj U) :
      (eqToHom e).val.app U ((eqToHom e.symm).val.app U z) = z := by
    cases e
    rfl
  rw [hc]
  congr 1
  exact hn.symm
end

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
private theorem scalar_obj : ∀ N : integralTowerModules.{u, u} l E Y,
    (integralOrdinaryScalar l E L ι Y).obj N = SheafOfModules.changeOfRings
      (integralCompletedScalarMap l E L ι Y) N := by
  unfold integralOrdinaryScalar
  exact (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose

private theorem tensorSection_eq (N : integralTowerModules.{u, u} l E Y)
    (U : Y.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : N.val.obj U) :
    tensorSection (integralCompletedScalarMap l E L ι Y)
      (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y) N U s x =
      integralOrdinaryTensorSection l E L ι Y N U s x := by
  unfold tensorSection integralOrdinaryTensorSection integralOrdinaryScalar
  rfl

private theorem scalar_map {N N' : integralTowerModules.{u, u} l E Y} (f : N ⟶ N') :
    (integralOrdinaryScalar l E L ι Y).map f =
      eqToHom (scalar_obj l E L ι Y N) ≫
        SheafOfModules.changeOfRingsHom (integralCompletedScalarMap l E L ι Y) N f ≫
          eqToHom (scalar_obj l E L ι Y N').symm := by
  unfold integralOrdinaryScalar
  exact (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose_spec.choose f

private theorem scalar_map_tensor {N N' : integralTowerModules.{u, u} l E Y}
    (f : N ⟶ N') (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
    (x : N.val.obj U) :
    ((integralOrdinaryScalar l E L ι Y).map f).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U s x) =
      integralOrdinaryTensorSection l E L ι Y N' U s (f.val.app U x) := by
  have ht := tensorSection_map (integralCompletedScalarMap l E L ι Y)
      (integralOrdinaryScalar l E L ι Y) (scalar_obj l E L ι Y)
      (scalar_map l E L ι Y) f U s x
  rw [tensorSection_eq, tensorSection_eq] at ht
  with_unfolding_all exact ht

variable
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)
private theorem scalar_comp_inv_tensor
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l M Y).obj.obj U)
    (x : N.val.obj U) :
    ((integralOrdinaryScalarComp l E L ι Y M j).inv.app N).val.app U
      (integralOrdinaryTensorSection l E M (j.comp ι) Y N U s x) =
    integralOrdinaryTensorSection l L M j Y _ U s
      (integralOrdinaryTensorSection l E L ι Y N U 1 x) := by
  let a := integralOrdinaryScalarComp l E L ι Y M j
  let z := integralOrdinaryTensorSection l L M j Y _ U s
    (integralOrdinaryTensorSection l E L ι Y N U 1 x)
  have hz : (a.hom.app N).val.app U z =
      integralOrdinaryTensorSection l E M (j.comp ι) Y N U s x := by
    simpa only [a, z, integralOrdinaryScalarComp] using
    ((integralOrdinaryScalarComp_existsUnique l E L ι Y M j).exists.choose_spec
      N U s 1 x).trans (by rw [map_one, mul_one])
  calc
    _ = (a.inv.app N).val.app U ((a.hom.app N).val.app U z) :=
      congrArg (fun y ↦ (a.inv.app N).val.app U y) hz.symm
    _ = z := congrArg (fun t ↦ t.val.app U z) (a.hom_inv_id_app N)

private theorem scalar_unit_inv_tensor
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ) (x : N.val.obj U) :
    ((integralOrdinaryScalarUnit l E Y).inv.app N).val.app U x =
      integralOrdinaryTensorSection l E E (AlgHom.id (Padic l) E) Y N U 1 x := by
  let a := integralOrdinaryScalarUnit l E Y
  let z := integralOrdinaryTensorSection l E E (AlgHom.id (Padic l) E) Y N U 1 x
  have hz : (a.hom.app N).val.app U z = x := by
    simpa only [a, z, integralOrdinaryScalarUnit] using
    ((integralOrdinaryScalarUnit_existsUnique l E Y).exists.choose_spec N U 1 x).trans
      (one_smul _ _)
  calc
    _ = (a.inv.app N).val.app U ((a.hom.app N).val.app U z) :=
      congrArg (fun y ↦ (a.inv.app N).val.app U y) hz.symm
    _ = z := congrArg (fun t ↦ t.val.app U z) (a.hom_inv_id_app N)

private theorem ordinary_source_unit :
    integralOrdinaryScalarComp l E E (AlgHom.id (Padic l) E) Y L ι =
      Functor.isoWhiskerRight (integralOrdinaryScalarUnit l E Y)
        (integralOrdinaryScalar l E L ι Y) ≪≫
      Functor.leftUnitor (integralOrdinaryScalar l E L ι Y) := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  apply NatTrans.ext
  funext N
  apply tensorSection_ext (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y)
    (scalar_obj l E L ι Y)
  intro U x
  rw [tensorSection_eq]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app]
  change ((integralOrdinaryScalarComp l E E (AlgHom.id (Padic l) E) Y L ι).inv.app N).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U 1 x) =
    ((integralOrdinaryScalar l E L ι Y).map
      ((integralOrdinaryScalarUnit l E Y).inv.app N)).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U 1 x)
  erw [scalar_comp_inv_tensor]
  erw [scalar_map_tensor]
  change _ = integralOrdinaryTensorSection l E L ι Y _ U 1
    (((integralOrdinaryScalarUnit l E Y).inv.app N).val.app U x)
  rw [scalar_unit_inv_tensor]

private theorem ordinary_target_unit :
    integralOrdinaryScalarComp l E L ι Y L (AlgHom.id (Padic l) L) =
      Functor.isoWhiskerLeft (integralOrdinaryScalar l E L ι Y)
        (integralOrdinaryScalarUnit l L Y) ≪≫
      Functor.rightUnitor (integralOrdinaryScalar l E L ι Y) := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  apply NatTrans.ext
  funext N
  apply tensorSection_ext (integralCompletedScalarMap l E L ι Y)
    (integralOrdinaryScalar l E L ι Y)
    (scalar_obj l E L ι Y)
  intro U x
  rw [tensorSection_eq]
  simp only [Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app]
  change ((integralOrdinaryScalarComp l E L ι Y L (AlgHom.id (Padic l) L)).inv.app N).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U 1 x) =
    ((integralOrdinaryScalarUnit l L Y).inv.app
      ((integralOrdinaryScalar l E L ι Y).obj N)).val.app U
      (integralOrdinaryTensorSection l E L ι Y N U 1 x)
  erw [scalar_comp_inv_tensor, scalar_unit_inv_tensor]

private theorem ordinary_pentagon
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (k : M →ₐ[Padic l] N) :
    Functor.isoWhiskerRight (integralOrdinaryScalarComp l E L ι Y M j)
        (integralOrdinaryScalar l M N k Y) ≪≫
      integralOrdinaryScalarComp l E M (j.comp ι) Y N k =
    Functor.isoWhiskerLeft (integralOrdinaryScalar l E L ι Y)
        (integralOrdinaryScalarComp l L M j Y N k) ≪≫
      integralOrdinaryScalarComp l E L ι Y N (k.comp j) := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  apply NatTrans.ext
  funext P
  apply tensorSection_ext (integralCompletedScalarMap l E N (k.comp (j.comp ι)) Y)
    (integralOrdinaryScalar l E N (k.comp (j.comp ι)) Y)
    (scalar_obj l E N (k.comp (j.comp ι)) Y)
  intro U x
  rw [tensorSection_eq]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change (((integralOrdinaryScalarComp l E M (j.comp ι) Y N k).inv.app P) ≫
    (integralOrdinaryScalar l M N k Y).map
      ((integralOrdinaryScalarComp l E L ι Y M j).inv.app P)).val.app U
      (integralOrdinaryTensorSection l E N (k.comp (j.comp ι)) Y P U 1 x) =
    (((integralOrdinaryScalarComp l E L ι Y N (k.comp j)).inv.app P) ≫
      (integralOrdinaryScalarComp l L M j Y N k).inv.app
        ((integralOrdinaryScalar l E L ι Y).obj P)).val.app U
      (integralOrdinaryTensorSection l E N (k.comp (j.comp ι)) Y P U 1 x)
  change ((integralOrdinaryScalar l M N k Y).map
    ((integralOrdinaryScalarComp l E L ι Y M j).inv.app P)).val.app U
      (((integralOrdinaryScalarComp l E M (j.comp ι) Y N k).inv.app P).val.app U
        (integralOrdinaryTensorSection l E N (k.comp (j.comp ι)) Y P U 1 x)) = _
  erw [scalar_comp_inv_tensor]
  erw [scalar_map_tensor]
  rw [scalar_comp_inv_tensor]
  change _ = ((integralOrdinaryScalarComp l L M j Y N k).inv.app
    ((integralOrdinaryScalar l E L ι Y).obj P)).val.app U
      (((integralOrdinaryScalarComp l E L ι Y N (k.comp j)).inv.app P).val.app U
        (integralOrdinaryTensorSection l E N (k.comp (j.comp ι)) Y P U 1 x))
  erw [scalar_comp_inv_tensor, scalar_comp_inv_tensor]
  rfl
end OrdinaryCoherence

section DerivedCoherence
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryScalarUnit
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategory

private theorem ordinary_derived_source_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E Y)) :
    (integralOrdinaryDerivedScalarComp l E E (AlgHom.id (Padic l) E) Y L ι).hom.app K =
      (integralOrdinaryDerivedScalar l E L ι Y).map
        ((integralOrdinaryDerivedScalarUnit l E Y).hom.app K) := by
  let A := integralTowerModules.{u, u} l E Y
  let B := integralTowerModules.{u, u} l L Y
  have derived_source_unit
    (T : A ⥤ A) (F : A ⥤ B)
    [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (u : T ≅ 𝟭 A) (a : T ⋙ F ≅ F)
    (ha : a = Functor.isoWhiskerRight u F ≪≫ Functor.leftUnitor F) :
      (Functor.mapDerivedCategoryCompIso T F ≪≫
        Functor.mapDerivedCategoryNatIso a).hom =
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso u ≪≫ Functor.mapDerivedCategoryIdIso A).hom
        F.mapDerivedCategory := by
    have h := Functor.mapDerivedCategoryNatIso_isoWhiskerRight u F
    have hu := Functor.mapDerivedCategoryCompIso_id_comp F
    have ha' : a = Functor.isoWhiskerRight u F := by
      apply Iso.ext
      apply NatTrans.ext
      funext X
      have hx := congrArg (fun e ↦ e.hom.app X) ha
      dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app] at hx
      erw [Category.comp_id] at hx
      exact hx
    rw [ha']
    apply (cancel_mono (Functor.mapDerivedCategoryCompIso (𝟭 A) F).inv).mp
    simp only [Iso.trans_hom, Category.assoc,
      Functor.whiskerRight_comp]
    rw [h]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    have hu' : Functor.whiskerRight (Functor.mapDerivedCategoryIdIso A).hom
        F.mapDerivedCategory ≫ (Functor.mapDerivedCategoryCompIso (𝟭 A) F).inv = 𝟙 _ := by
      apply (cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 A) F).inv).mp
      rw [← Category.assoc, hu]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    rw [Category.assoc, hu', Category.comp_id]
  have h := derived_source_unit
      (integralOrdinaryScalar l E E (AlgHom.id (Padic l) E) Y)
      (integralOrdinaryScalar l E L ι Y) (integralOrdinaryScalarUnit l E Y)
      (integralOrdinaryScalarComp l E E (AlgHom.id (Padic l) E) Y L ι)
      (ordinary_source_unit l E L ι Y)
  exact congrArg (fun t ↦ t.app K) h

private theorem ordinary_derived_target_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E Y)) :
    (integralOrdinaryDerivedScalarComp l E L ι Y L (AlgHom.id (Padic l) L)).hom.app K =
      (integralOrdinaryDerivedScalarUnit l L Y).hom.app
        ((integralOrdinaryDerivedScalar l E L ι Y).obj K) := by
  let A := integralTowerModules.{u, u} l E Y
  let B := integralTowerModules.{u, u} l L Y
  have derived_target_unit
    (F : A ⥤ B) (T : B ⥤ B)
    [T.Additive] [F.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (u : T ≅ 𝟭 B) (a : F ⋙ T ≅ F)
    (ha : a = Functor.isoWhiskerLeft F u ≪≫ Functor.rightUnitor F) :
      (Functor.mapDerivedCategoryCompIso F T ≪≫
        Functor.mapDerivedCategoryNatIso a).hom =
      Functor.whiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso u ≪≫ Functor.mapDerivedCategoryIdIso B).hom := by
    have h := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F u
    have hu := Functor.mapDerivedCategoryCompIso_comp_id F
    have ha' : a = Functor.isoWhiskerLeft F u := by
      apply Iso.ext
      apply NatTrans.ext
      funext X
      have hx := congrArg (fun e ↦ e.hom.app X) ha
      dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_hom_app] at hx
      erw [Category.comp_id] at hx
      exact hx
    rw [ha']
    apply (cancel_mono (Functor.mapDerivedCategoryCompIso F (𝟭 B)).inv).mp
    simp only [Iso.trans_hom, Category.assoc,
      Functor.whiskerLeft_comp]
    rw [h]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    have hu' : Functor.whiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryIdIso B).hom ≫
        (Functor.mapDerivedCategoryCompIso F (𝟭 B)).inv = 𝟙 _ := by
      apply (cancel_epi (Functor.mapDerivedCategoryCompIso F (𝟭 B)).inv).mp
      rw [← Category.assoc, hu]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    rw [Category.assoc, hu', Category.comp_id]
  have h := derived_target_unit
      (integralOrdinaryScalar l E L ι Y)
      (integralOrdinaryScalar l L L (AlgHom.id (Padic l) L) Y)
      (integralOrdinaryScalarUnit l L Y)
      (integralOrdinaryScalarComp l E L ι Y L (AlgHom.id (Padic l) L))
      (ordinary_target_unit l E L ι Y)
  exact congrArg (fun t ↦ t.app K) h

private theorem ordinary_derived_pentagon
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (j : L →ₐ[Padic l] M)
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (k : M →ₐ[Padic l] N)
    (K : DerivedCategory (integralTowerModules.{u, u} l E Y)) :
    (integralOrdinaryDerivedScalar l M N k Y).map
        ((integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K) ≫
      (integralOrdinaryDerivedScalarComp l E M (j.comp ι) Y N k).hom.app K =
    (integralOrdinaryDerivedScalarComp l L M j Y N k).hom.app
        ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
      (integralOrdinaryDerivedScalarComp l E L ι Y N (k.comp j)).hom.app K := by
  exact Functor.mapDerivedCategoryCompNatIso_cocycle
    (integralOrdinaryScalarComp l E L ι Y M j)
    (integralOrdinaryScalarComp l E M (j.comp ι) Y N k)
    (integralOrdinaryScalarComp l L M j Y N k)
    (integralOrdinaryScalarComp l E L ι Y N (k.comp j))
    (fun X ↦ congrArg (fun e ↦ e.hom.app X) (ordinary_pentagon l E L ι Y M j N k)) K

end DerivedCoherence

private theorem conj_unit_left {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (I : A ⥤ B) (J : C ⥤ D)
    (T : A ⥤ A) (F : A ⥤ C) (T₀ : B ⥤ B) (F₀ : B ⥤ D)
    (c : I ⋙ T₀ ≅ T ⋙ I) (d : I ⋙ F₀ ≅ F ⋙ J)
    (u₀ : T₀ ≅ 𝟭 B) (u : T ≅ 𝟭 A)
    (hu' : ∀ K, I.map (u.hom.app K) = c.inv.app K ≫ u₀.hom.app (I.obj K))
    (K : A) :
    d.inv.app (T.obj K) ≫ F₀.map (c.inv.app K) ≫
      F₀.map (u₀.hom.app (I.obj K)) ≫ d.hom.app K =
      J.map (F.map (u.hom.app K)) := by
  rw [← F₀.map_comp_assoc, ← hu']
  have hn := d.hom.naturality (u.hom.app K)
  change F₀.map (I.map (u.hom.app K)) ≫ d.hom.app K =
    d.hom.app (T.obj K) ≫ J.map (F.map (u.hom.app K)) at hn
  rw [hn, Iso.inv_hom_id_app_assoc]
private theorem conj_unit_right {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (I : A ⥤ B) (J : C ⥤ D)
    (T : C ⥤ C) (F : A ⥤ C) (T₀ : D ⥤ D) (F₀ : B ⥤ D)
    (c : J ⋙ T₀ ≅ T ⋙ J) (d : I ⋙ F₀ ≅ F ⋙ J)
    (u₀ : T₀ ≅ 𝟭 D) (K : A) :
    c.inv.app (F.obj K) ≫ T₀.map (d.inv.app K) ≫
      u₀.hom.app (F₀.obj (I.obj K)) ≫ d.hom.app K =
      c.inv.app (F.obj K) ≫ u₀.hom.app (J.obj (F.obj K)) := by
  rw [reassoc_of% (u₀.hom.naturality (d.inv.app K))]
  simp only [Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem conj_comp {A B C D A₀ B₀ C₀ D₀ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    (I : A ⥤ A₀) (J : B ⥤ B₀) (K : C ⥤ C₀) (L : D ⥤ D₀)
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    (FG : A ⥤ C) (GH : B ⥤ D) (FGH : A ⥤ D)
    (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ C₀) (H₀ : C₀ ⥤ D₀)
    (FG₀ : A₀ ⥤ C₀) (GH₀ : B₀ ⥤ D₀) (FGH₀ : A₀ ⥤ D₀)
    (cF : I ⋙ F₀ ≅ F ⋙ J) (cG : J ⋙ G₀ ≅ G ⋙ K)
    (cH : K ⋙ H₀ ≅ H ⋙ L) (cFG : I ⋙ FG₀ ≅ FG ⋙ K)
    (cGH : J ⋙ GH₀ ≅ GH ⋙ L) (cFGH : I ⋙ FGH₀ ≅ FGH ⋙ L)
    (a₀ : F₀ ⋙ G₀ ≅ FG₀) (b₀ : FG₀ ⋙ H₀ ≅ FGH₀)
    (c₀ : G₀ ⋙ H₀ ≅ GH₀) (d₀ : F₀ ⋙ GH₀ ≅ FGH₀)
    (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH)
    (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
    (ha : ∀ X, K.map (a.hom.app X) = cG.inv.app (F.obj X) ≫
      G₀.map (cF.inv.app X) ≫ a₀.hom.app (I.obj X) ≫ cFG.hom.app X)
    (hb : ∀ X, L.map (b.hom.app X) = cH.inv.app (FG.obj X) ≫
      H₀.map (cFG.inv.app X) ≫ b₀.hom.app (I.obj X) ≫ cFGH.hom.app X)
    (hc : ∀ X, L.map (c.hom.app X) = cH.inv.app (G.obj X) ≫
      H₀.map (cG.inv.app X) ≫ c₀.hom.app (J.obj X) ≫ cGH.hom.app X)
    (hd : ∀ X, L.map (d.hom.app X) = cGH.inv.app (F.obj X) ≫
      GH₀.map (cF.inv.app X) ≫ d₀.hom.app (I.obj X) ≫ cFGH.hom.app X)
    (h₀ : ∀ X, H₀.map (a₀.hom.app X) ≫ b₀.hom.app X =
      c₀.hom.app (F₀.obj X) ≫ d₀.hom.app X) (X : A) :
    L.map (H.map (a.hom.app X) ≫ b.hom.app X) =
      L.map (c.hom.app (F.obj X) ≫ d.hom.app X) := by
  have hn := cH.hom.naturality (a.hom.app X)
  have hm : L.map (H.map (a.hom.app X)) =
      cH.inv.app (G.obj (F.obj X)) ≫ H₀.map (K.map (a.hom.app X)) ≫
        cH.hom.app (FG.obj X) := by
    have hn' : H₀.map (K.map (a.hom.app X)) ≫ cH.hom.app (FG.obj X) =
        cH.hom.app (G.obj (F.obj X)) ≫ L.map (H.map (a.hom.app X)) := hn
    rw [hn']
    simp only [Iso.inv_hom_id_app_assoc]
  rw [L.map_comp, L.map_comp, hm, ha, hb, hc, hd]
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  have hcanc : H₀.map (cFG.hom.app X) ≫ H₀.map (cFG.inv.app X) = 𝟙 _ := by
    rw [← H₀.map_comp, Iso.hom_inv_id_app, H₀.map_id]
  rw [← Category.assoc (H₀.map (cFG.hom.app X)) (H₀.map (cFG.inv.app X)), hcanc]
  erw [Category.id_comp]
  have hn' := c₀.hom.naturality (cF.inv.app X)
  change H₀.map (G₀.map (cF.inv.app X)) ≫ c₀.hom.app (F₀.obj (I.obj X)) =
    c₀.hom.app (J.obj (F.obj X)) ≫ GH₀.map (cF.inv.app X) at hn'
  calc
    _ = cH.inv.app (G.obj (F.obj X)) ≫ H₀.map (cG.inv.app (F.obj X)) ≫
        H₀.map (G₀.map (cF.inv.app X)) ≫
        (H₀.map (a₀.hom.app (I.obj X)) ≫ b₀.hom.app (I.obj X)) ≫
        cFGH.hom.app X := by simp only [Category.assoc]
    _ = _ := by rw [h₀]; simp only [Category.assoc]; rw [reassoc_of% hn']

private theorem conjugateComp_existsUnique
    {A B C A₀ B₀ C₀ : Type*}
    [Category A] [Category B] [Category C]
    [Category A₀] [Category B₀] [Category C₀]
    (I : A ⥤ A₀) (J : B ⥤ B₀) (K : C ⥤ C₀) [K.Full] [K.Faithful]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ C₀) (H₀ : A₀ ⥤ C₀)
    (c : I ⋙ F₀ ≅ F ⋙ J) (d : J ⋙ G₀ ≅ G ⋙ K) (e : I ⋙ H₀ ≅ H ⋙ K)
    (a₀ : F₀ ⋙ G₀ ≅ H₀) :
    ∃! a : F ⋙ G ≅ H, ∀ X, K.map (a.hom.app X) =
      d.inv.app (F.obj X) ≫ G₀.map (c.inv.app X) ≫ a₀.hom.app (I.obj X) ≫
        e.hom.app X := by
  let b : (F ⋙ G) ⋙ K ≅ H ⋙ K :=
    Functor.isoWhiskerLeft F d.symm ≪≫ (Functor.associator F J G₀).symm ≪≫
      Functor.isoWhiskerRight c.symm G₀ ≪≫ Functor.associator I F₀ G₀ ≪≫
        Functor.isoWhiskerLeft I a₀ ≪≫ e
  let a := Functor.fullyFaithfulCancelRight K b
  have ha (X) : K.map (a.hom.app X) =
      d.inv.app (F.obj X) ≫ G₀.map (c.inv.app X) ≫ a₀.hom.app (I.obj X) ≫
        e.hom.app X := by
    dsimp only [a, Functor.fullyFaithfulCancelRight_hom_app]
    rw [K.map_preimage]
    simp [b]
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact K.map_injective ((ha' X).trans (ha X).symm)

private theorem conjugateUnit_existsUnique
    {A B : Type*} [Category A] [Category B]
    (I : A ⥤ B) [I.Full] [I.Faithful] (F : A ⥤ A) (F₀ : B ⥤ B)
    (c : I ⋙ F₀ ≅ F ⋙ I) (u₀ : F₀ ≅ 𝟭 B) :
    ∃! a : F ≅ 𝟭 A, ∀ X, I.map (a.hom.app X) =
      c.inv.app X ≫ u₀.hom.app (I.obj X) := by
  let b : F ⋙ I ≅ (𝟭 A) ⋙ I := c.symm ≪≫
    Functor.isoWhiskerLeft I u₀ ≪≫ Functor.rightUnitor I ≪≫ (Functor.leftUnitor I).symm
  let a := Functor.fullyFaithfulCancelRight I b
  have ha (X) : I.map (a.hom.app X) = c.inv.app X ≫ u₀.hom.app (I.obj X) := by
    dsimp only [a, Functor.fullyFaithfulCancelRight_hom_app]
    rw [I.map_preimage]
    simp [b]
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact I.map_injective ((ha' X).trans (ha X).symm)

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have hc (K) : HEq (c K).hom
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
    simp [c]
  have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
      F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
    obtain ⟨K⟩ := K
    obtain ⟨K'⟩ := K'
    induction f using TensorProduct.inductionOn with
    | add f g hf hg =>
      rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      rw [(conj_eqToHom_iff_heq _ _ (hF ⟨K⟩) (hF ⟨K'⟩)).mpr (mF K K' f a),
        (conj_eqToHom_iff_heq _ _ (hG ⟨K⟩) (hG ⟨K'⟩)).mpr (mG K K' f a)]
      dsimp [c]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have he : ScalarLocalization.composition S D v _ _ _
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
          ScalarLocalization.composition S D v _ _ _
            (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
        rw [e.hom.naturality f]
      have he' :
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
            (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
      simpa only [ScalarLocalization.localization, Category.assoc] using
        congrArg (fun z :
          (⟨F₀.obj K⟩ : ScalarLocalization S D v) ⟶ ⟨G₀.obj K'⟩ ↦
            eqToHom (hF ⟨K⟩) ≫ z ≫ eqToHom (hG ⟨K'⟩).symm) he'
  let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
  refine ⟨a, hc, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((ha' K).trans (hc K).symm)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The normalized ordinary-to-completed comparison on intrinsic integral objects.
Source: blueprint order 1828, proof, first paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: the finite-free completed-scalar comparison in the DAG identifies ordinary derived
extension and completed extension on every derived-complete input. On a K-flat complex
with flat terms, its map is the quotient-completion chain map: its unshifted cone
coordinates are the finite quotient tensor maps, and its shifted coordinate is zero.
Finite freeness commutes with the products in the Roos complex; completeness and cofinality
of the two uniformizer filtrations show this very map is invertible. The intrinsic predicate
includes derived completeness, so this applies without a finite-field structure on Y.
Naturality for good complexes descends through roofs. Every object has a good resolution,
so the displayed representative characterization determines the comparison uniquely. -/
theorem sfIntegralOrdinaryComparison_existsUnique :
    ∃! c : (sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y ≅
        (sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y,
      ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj)),
        c.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
  classical
  let χ := scalarCompletion.{u} l E L ι Y
  have hχ := (scalarCompletion_existsUnique.{u} l E L ι Y).exists.choose_spec
  let F := (sfIntegralConstructible l E Y).ι
  have (K : sfIntegralConstructibleCategory l E Y) : IsIso (χ.app K.obj) :=
    hχ.2 K.obj K.property.1
  let c : F ⋙ integralOrdinaryDerivedScalar l E L ι Y ≅
      F ⋙ integralScalarExtension l E L ι Y :=
    NatIso.ofComponents (fun K ↦ asIso (χ.app K.obj))
      (fun f ↦ χ.naturality f.hom)
  refine ⟨c, ?_, ?_⟩
  · intro P hP
    exact hχ.1 P
  · intro c' hc'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    let Q := DerivedCategory.Q (C := integralTowerModules.{u, u} l E Y)
    let T := Q.objPreimage K.obj
    let e := Q.objObjPreimageIso K.obj
    let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
    let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y
    let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
    let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
    obtain ⟨P, f, hflat, hterms, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u+1, u+1, u}
        (C := Y.ProEt) (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) T
    have : QuasiIso f := hf
    let e' : Q.obj P ≅ K.obj := asIso (Q.map f) ≪≫ e
    have hP : sfIntegralConstructible l E Y (Q.obj P) :=
      (sfIntegralConstructible l E Y).prop_of_iso e'.symm K.property
    have hg : integralOperationsGoodComplex.{u, u} l E Y P :=
      ⟨hflat, fun i ↦ (CategoryTheory.exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso.{u+1, u, u+1}
          (completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) (P.X i)).symm (hterms i)⟩
    let A : sfIntegralConstructibleCategory l E Y := ⟨Q.obj P, hP⟩
    let a : A ≅ K :=
      { hom := ⟨e'.hom⟩
        inv := ⟨e'.inv⟩
        hom_inv_id := by ext; exact e'.hom_inv_id
        inv_hom_id := by ext; exact e'.inv_hom_id }
    have heq : c'.hom.app A = c.hom.app A := by
      apply (cancel_mono ((integralScalarExtensionComparison l E L ι Y).hom.app
        ⟨P, hg⟩)).mp
      exact (hc' ⟨P, hg⟩ hP).trans (hχ.1 ⟨P, hg⟩).symm
    let ea := (F ⋙ integralOrdinaryDerivedScalar l E L ι Y).mapIso a
    have : IsIso ea.hom := ea.isIso_hom
    apply (cancel_epi ea.hom).mp
    exact (c'.hom.naturality a.hom).trans
      ((congrArg (fun z ↦ z ≫ (F ⋙ integralScalarExtension l E L ι Y).map a.hom)
        heq).trans (c.hom.naturality a.hom).symm)

/-- The uniquely normalized comparison; its data is fixed by quotient maps on good complexes.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralOrdinaryComparison :=
  (sfIntegralOrdinaryComparison_existsUnique l E L ι Y).exists.choose

variable (p : ℕ) (hl : l ≠ p)
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

/-- Completed integral associativity, uniquely fixed by ordinary balanced tensor and the
normalized quotient-completion comparisons.
Source: blueprint order 1828, proof, first paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: on a K-flat resolution, ordinary associativity sends c tensor (b tensor x) to
c*j(b) tensor x, with inverse c tensor x to c tensor (1 tensor x). These maps commute
with restrictions, differentials and chain maps, hence descend through roofs. Conjugate
this fixed ordinary associator by the three normalized ordinary-to-completed comparisons.
Completed extension preserves the intrinsic subcategories, so full faithfulness of their
inclusions lifts this isomorphism and its inverse uniquely. The displayed equation specifies
that lift, rather than choosing an unnormalized natural isomorphism. -/
theorem sfIntegralScalarComp_existsUnique :
    ∃! a : sfConstructibleIntegralScalarExtension p l hl E L ι Y ⋙
        sfConstructibleIntegralScalarExtension p l hl L M j Y ≅
        sfConstructibleIntegralScalarExtension p l hl E M (j.comp ι) Y,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        (a.hom.app K).hom =
          (sfIntegralOrdinaryComparison l L M j Y).inv.app
              ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K) ≫
            (integralOrdinaryDerivedScalar l L M j Y).map
              ((sfIntegralOrdinaryComparison l E L ι Y).inv.app K) ≫
            (integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K.obj ≫
            (sfIntegralOrdinaryComparison l E M (j.comp ι) Y).hom.app K := by
  exact conjugateComp_existsUnique
    (sfIntegralConstructible l E Y).ι (sfIntegralConstructible l L Y).ι
    (sfIntegralConstructible l M Y).ι
    (sfConstructibleIntegralScalarExtension p l hl E L ι Y)
    (sfConstructibleIntegralScalarExtension p l hl L M j Y)
    (sfConstructibleIntegralScalarExtension p l hl E M (j.comp ι) Y)
    (integralOrdinaryDerivedScalar l E L ι Y) (integralOrdinaryDerivedScalar l L M j Y)
    (integralOrdinaryDerivedScalar l E M (j.comp ι) Y)
    (sfIntegralOrdinaryComparison l E L ι Y) (sfIntegralOrdinaryComparison l L M j Y)
    (sfIntegralOrdinaryComparison l E M (j.comp ι) Y)
    (integralOrdinaryDerivedScalarComp l E L ι Y M j)

/-- The intrinsic completed integral associator with its fixed tensor normalization.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralScalarComp :=
  (sfIntegralScalarComp_existsUnique l E L ι Y p hl M j).exists.choose

/-- The completed integral identity comparison, uniquely normalized by multiplication.
Source: blueprint order 1828, proof, identity-extension clause
(blueprint: lem-weil-scalar-extension-composition).
Proof: the ordinary unit sends s tensor x to s*x, with inverse x to 1 tensor x.
Conjugating it by the identity ordinary-to-completed comparison gives the actual
completeness-unit normalization. Full faithfulness lifts it uniquely to the intrinsic
subcategory; the inverse is the lift of the inverse ambient map. -/
theorem sfIntegralScalarUnit_existsUnique :
    ∃! a : sfConstructibleIntegralScalarExtension p l hl E E (AlgHom.id (Padic l) E) Y ≅
        𝟭 (sfIntegralConstructibleCategory l E Y),
      ∀ K : sfIntegralConstructibleCategory l E Y,
        (a.hom.app K).hom =
          (sfIntegralOrdinaryComparison l E E (AlgHom.id (Padic l) E) Y).inv.app K ≫
            (integralOrdinaryDerivedScalarUnit l E Y).hom.app K.obj := by
  exact conjugateUnit_existsUnique (sfIntegralConstructible l E Y).ι
    (sfConstructibleIntegralScalarExtension p l hl E E (AlgHom.id (Padic l) E) Y)
    (integralOrdinaryDerivedScalar l E E (AlgHom.id (Padic l) E) Y)
    (sfIntegralOrdinaryComparison l E E (AlgHom.id (Padic l) E) Y)
    (integralOrdinaryDerivedScalarUnit l E Y)

/-- The normalized intrinsic integral unit.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralScalarUnit :=
  (sfIntegralScalarUnit_existsUnique l E Y p hl).exists.choose

private theorem integral_source_unit
    (K : sfIntegralConstructibleCategory l E Y) :
    (sfIntegralScalarComp l E E (AlgHom.id (Padic l) E) Y p hl L ι).hom.app K =
      (sfConstructibleIntegralScalarExtension p l hl E L ι Y).map
        ((sfIntegralScalarUnit l E Y p hl).hom.app K) := by
  apply (sfIntegralConstructible l L Y).ι.map_injective
  rw [show (sfIntegralConstructible l L Y).ι.map
      ((sfIntegralScalarComp l E E (AlgHom.id (Padic l) E) Y p hl L ι).hom.app K) = _ from
    (sfIntegralScalarComp_existsUnique l E E
      (AlgHom.id (Padic l) E) Y p hl L ι).exists.choose_spec K]
  rw [ordinary_derived_source_unit]
  exact conj_unit_left (sfIntegralConstructible l E Y).ι
    (sfIntegralConstructible l L Y).ι
    (sfConstructibleIntegralScalarExtension p l hl E E (AlgHom.id (Padic l) E) Y)
    (sfConstructibleIntegralScalarExtension p l hl E L ι Y)
    (integralOrdinaryDerivedScalar l E E (AlgHom.id (Padic l) E) Y)
    (integralOrdinaryDerivedScalar l E L ι Y)
    (sfIntegralOrdinaryComparison l E E (AlgHom.id (Padic l) E) Y)
    (sfIntegralOrdinaryComparison l E L ι Y)
    (integralOrdinaryDerivedScalarUnit l E Y) (sfIntegralScalarUnit l E Y p hl)
    (sfIntegralScalarUnit_existsUnique l E Y p hl).exists.choose_spec K

private theorem integral_target_unit
    (K : sfIntegralConstructibleCategory l E Y) :
    (sfIntegralScalarComp l E L ι Y p hl L (AlgHom.id (Padic l) L)).hom.app K =
      (sfIntegralScalarUnit l L Y p hl).hom.app
        ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K) := by
  apply (sfIntegralConstructible l L Y).ι.map_injective
  rw [show (sfIntegralConstructible l L Y).ι.map
      ((sfIntegralScalarComp l E L ι Y p hl L (AlgHom.id (Padic l) L)).hom.app K) = _ from
    (sfIntegralScalarComp_existsUnique l E L ι Y p hl L
      (AlgHom.id (Padic l) L)).exists.choose_spec K]
  rw [ordinary_derived_target_unit]
  rw [show (sfIntegralConstructible l L Y).ι.map
      ((sfIntegralScalarUnit l L Y p hl).hom.app
        ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K)) = _ from
    (sfIntegralScalarUnit_existsUnique l L Y p hl).exists.choose_spec _]
  exact conj_unit_right (sfIntegralConstructible l E Y).ι
    (sfIntegralConstructible l L Y).ι
    (sfConstructibleIntegralScalarExtension p l hl L L (AlgHom.id (Padic l) L) Y)
    (sfConstructibleIntegralScalarExtension p l hl E L ι Y)
    (integralOrdinaryDerivedScalar l L L (AlgHom.id (Padic l) L) Y)
    (integralOrdinaryDerivedScalar l E L ι Y)
    (sfIntegralOrdinaryComparison l L L (AlgHom.id (Padic l) L) Y)
    (sfIntegralOrdinaryComparison l E L ι Y) (integralOrdinaryDerivedScalarUnit l L Y) K

private theorem integral_pentagon
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (k : M →ₐ[Padic l] N) (K : sfIntegralConstructibleCategory l E Y) :
    (sfConstructibleIntegralScalarExtension p l hl M N k Y).map
        ((sfIntegralScalarComp l E L ι Y p hl M j).hom.app K) ≫
      (sfIntegralScalarComp l E M (j.comp ι) Y p hl N k).hom.app K =
    (sfIntegralScalarComp l L M j Y p hl N k).hom.app
        ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K) ≫
      (sfIntegralScalarComp l E L ι Y p hl N (k.comp j)).hom.app K := by
  apply (sfIntegralConstructible l N Y).ι.map_injective
  exact conj_comp
    (sfIntegralConstructible l E Y).ι (sfIntegralConstructible l L Y).ι
    (sfIntegralConstructible l M Y).ι (sfIntegralConstructible l N Y).ι
    (sfConstructibleIntegralScalarExtension p l hl E L ι Y)
    (sfConstructibleIntegralScalarExtension p l hl L M j Y)
    (sfConstructibleIntegralScalarExtension p l hl M N k Y)
    (sfConstructibleIntegralScalarExtension p l hl E M (j.comp ι) Y)
    (sfConstructibleIntegralScalarExtension p l hl L N (k.comp j) Y)
    (sfConstructibleIntegralScalarExtension p l hl E N (k.comp (j.comp ι)) Y)
    (integralOrdinaryDerivedScalar l E L ι Y) (integralOrdinaryDerivedScalar l L M j Y)
    (integralOrdinaryDerivedScalar l M N k Y)
    (integralOrdinaryDerivedScalar l E M (j.comp ι) Y)
    (integralOrdinaryDerivedScalar l L N (k.comp j) Y)
    (integralOrdinaryDerivedScalar l E N (k.comp (j.comp ι)) Y)
    (sfIntegralOrdinaryComparison l E L ι Y) (sfIntegralOrdinaryComparison l L M j Y)
    (sfIntegralOrdinaryComparison l M N k Y)
    (sfIntegralOrdinaryComparison l E M (j.comp ι) Y)
    (sfIntegralOrdinaryComparison l L N (k.comp j) Y)
    (sfIntegralOrdinaryComparison l E N (k.comp (j.comp ι)) Y)
    (integralOrdinaryDerivedScalarComp l E L ι Y M j)
    (integralOrdinaryDerivedScalarComp l E M (j.comp ι) Y N k)
    (integralOrdinaryDerivedScalarComp l L M j Y N k)
    (integralOrdinaryDerivedScalarComp l E L ι Y N (k.comp j))
    (sfIntegralScalarComp l E L ι Y p hl M j)
    (sfIntegralScalarComp l E M (j.comp ι) Y p hl N k)
    (sfIntegralScalarComp l L M j Y p hl N k)
    (sfIntegralScalarComp l E L ι Y p hl N (k.comp j))
    (sfIntegralScalarComp_existsUnique l E L ι Y p hl M j).exists.choose_spec
    (sfIntegralScalarComp_existsUnique l E M (j.comp ι) Y p hl N k).exists.choose_spec
    (sfIntegralScalarComp_existsUnique l L M j Y p hl N k).exists.choose_spec
    (sfIntegralScalarComp_existsUnique l E L ι Y p hl N (k.comp j)).exists.choose_spec
    (ordinary_derived_pentagon l E L ι Y M j N k) K

/-- The rational associator is uniquely specified as the image of the normalized
completed integral associator on every unchanged integral object.
Source: blueprint order 1828, proof, second paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: rationalization has the same objects, and its morphisms are generated by pure
tensors f tensor a. Tensor each component of the integral associator and its inverse
with one. Integral naturality is linear over the source integers, so multiplying it
by a and adding proves naturality for every rational morphism. The inverse equations
survive localization. The published scalar functor has precisely the prescribed integral
object map; transport along that equality gives the displayed HEq. Every object is an
integral representative, so the component condition uniquely determines the isomorphism. -/
theorem sfRationalScalarComp_existsUnique :
    ∃! a : sfRationalScalarExtension l E Y p hl L ι ⋙
        sfRationalScalarExtension l L Y p hl M j ≅
        sfRationalScalarExtension l E Y p hl M (j.comp ι),
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (a.hom.app K)
          ((sfRationalConstructibleLocalization l M Y).map
            ((sfIntegralScalarComp l E L ι Y p hl M j).hom.app K.obj)) := by
  let F₀ := sfConstructibleIntegralScalarExtension p l hl E L ι Y
  let G₀ := sfConstructibleIntegralScalarExtension p l hl L M j Y
  let H₀ := sfConstructibleIntegralScalarExtension p l hl E M (j.comp ι) Y
  let F := sfRationalScalarExtension l E Y p hl L ι
  let G := sfRationalScalarExtension l L Y p hl M j
  let H := sfRationalScalarExtension l E Y p hl M (j.comp ι)
  have hF := (sfRationalScalarExtension_existsUnique l E Y p hl L ι).exists.choose_spec
  have hG := (sfRationalScalarExtension_existsUnique l L Y p hl M j).exists.choose_spec
  have hH := (sfRationalScalarExtension_existsUnique l E Y p hl M
    (j.comp ι)).exists.choose_spec
  let ψ a := (sfRationalCoefficientEquiv l M).symm
    ((j.comp ι) (sfRationalCoefficientEquiv l E a))
  apply localizedIso
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l M)
    ψ (F₀ ⋙ G₀) H₀ (sfIntegralScalarComp l E L ι Y p hl M j) (F ⋙ G) H
  · intro K
    exact (hG.2.1 (F.obj K)).trans
      (congrArg (fun X : sfRationalConstructibleCategory l L Y ↦
        (⟨G₀.obj X.obj⟩ : sfRationalConstructibleCategory l M Y)) (hF.2.1 K))
  · exact hH.2.1
  · intro K K' f a
    have hm := map_heq G (hF.2.1 ⟨K⟩) (hF.2.1 ⟨K'⟩) (hF.2.2 K K' f a)
    have hn := hG.2.2 (F₀.obj K) (F₀.obj K') (F₀.map f)
      ((sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a)))
    exact hm.trans (by
      simpa only [ψ, AlgEquiv.apply_symm_apply, AlgHom.comp_apply,
        sfRationalConstructibleLocalization, ScalarLocalization.localization,
        sfRationalScalarExtension, F₀, G₀, G, Functor.comp_obj, Functor.comp_map] using hn)
  · exact hH.2.2

/-- Canonical composition for the currently recorded rational scalar extensions.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfRationalScalarComp :
    sfRationalScalarExtension l E Y p hl L ι ⋙ sfRationalScalarExtension l L Y p hl M j ≅
      sfRationalScalarExtension l E Y p hl M (j.comp ι) :=
  (sfRationalScalarComp_existsUnique l E L ι Y p hl M j).exists.choose

/-- The rational unit is the localized normalized integral unit on every object.
Source: blueprint order 1828, proof, identity-extension clause
(blueprint: lem-weil-scalar-extension-composition).
Proof: localize the integral unit and inverse. Integral naturality multiplied by each
coefficient proves rational naturality on pure tensors and hence on every morphism.
The scalar functor's specified object equalities identify the endpoints, giving HEq.
All objects are integral representatives, so this condition proves uniqueness. -/
theorem sfRationalScalarUnit_existsUnique :
    ∃! a : sfRationalScalarExtension l E Y p hl E (AlgHom.id (Padic l) E) ≅
        𝟭 (sfRationalConstructibleCategory l E Y),
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (a.hom.app K)
          ((sfRationalConstructibleLocalization l E Y).map
            ((sfIntegralScalarUnit l E Y p hl).hom.app K.obj)) := by
  let F := sfRationalScalarExtension l E Y p hl E (AlgHom.id (Padic l) E)
  let F₀ := sfConstructibleIntegralScalarExtension p l hl E E
    (AlgHom.id (Padic l) E) Y
  have hobj := (sfRationalScalarExtension_existsUnique l E Y p hl E
    (AlgHom.id (Padic l) E)).exists.choose_spec.2.1
  have hmap := (sfRationalScalarExtension_existsUnique l E Y p hl E
    (AlgHom.id (Padic l) E)).exists.choose_spec.2.2
  apply localizedIso
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l E)
    id F₀ (𝟭 _) (sfIntegralScalarUnit l E Y p hl) F (𝟭 _)
    hobj (fun _ ↦ rfl)
  · intro K K' f a
    simpa only [F, F₀, id_eq, AlgHom.id_apply, AlgEquiv.symm_apply_apply,
      sfRationalConstructibleLocalization, ScalarLocalization.localization,
      sfRationalScalarExtension]
      using hmap K K' f a
  · intro K K' f a
    rfl

/-- The rational identity comparison, retaining the completeness-unit normalization.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfRationalScalarUnit :
    sfRationalScalarExtension l E Y p hl E (AlgHom.id (Padic l) E) ≅
      𝟭 (sfRationalConstructibleCategory l E Y) :=
  (sfRationalScalarUnit_existsUnique l E Y p hl).exists.choose

private theorem rational_obj
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l E Y p hl L ι).obj K =
      ⟨(sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K.obj⟩ :=
  (sfRationalScalarExtension_existsUnique l E Y p hl L ι).exists.choose_spec.2.1 K

private theorem rational_obj_comp
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l L Y p hl M j).obj
        ((sfRationalScalarExtension l E Y p hl L ι).obj K) =
      ⟨(sfConstructibleIntegralScalarExtension p l hl L M j Y).obj
        ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K.obj)⟩ := by
  rw [rational_obj, rational_obj]

private theorem rational_map_localization
    {K K' : sfIntegralConstructibleCategory l E Y} (f : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E Y p hl L ι).map
      ((sfRationalConstructibleLocalization l E Y).map f))
      ((sfRationalConstructibleLocalization l L Y).map
        ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).map f)) := by
  simpa only [sfRationalScalarExtension, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, map_one] using
    (sfRationalScalarExtension_existsUnique l E Y p hl L ι).exists.choose_spec.2.2 K K' f 1

private theorem app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X X' : C} (h : X = X') :
    HEq (α.app X) (α.app X') := by
  cases h
  rfl

private theorem comp_heq {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hX
  cases hY
  cases hZ
  cases hf
  cases hg
  rfl

private theorem rational_comp_component
    (K : sfRationalConstructibleCategory l E Y) :
    HEq ((sfRationalScalarComp l E L ι Y p hl M j).hom.app K)
      ((sfRationalConstructibleLocalization l M Y).map
        ((sfIntegralScalarComp l E L ι Y p hl M j).hom.app K.obj)) :=
  (sfRationalScalarComp_existsUnique l E L ι Y p hl M j).exists.choose_spec K

private theorem rational_unit_component
    (K : sfRationalConstructibleCategory l E Y) :
    HEq ((sfRationalScalarUnit l E Y p hl).hom.app K)
      ((sfRationalConstructibleLocalization l E Y).map
        ((sfIntegralScalarUnit l E Y p hl).hom.app K.obj)) :=
  (sfRationalScalarUnit_existsUnique l E Y p hl).exists.choose_spec K

attribute [local irreducible] sfRationalScalarComp
  sfRationalScalarUnit sfIntegralScalarComp sfIntegralScalarUnit

/-- Both identity-extension laws and the pentagon for the canonical intrinsic comparisons.
Source: blueprint order 1828, proof, unit and pentagon clauses
(blueprint: lem-weil-scalar-extension-composition).
Proof: check ordinary sheaf tensor generators. For a source identity, the associator
sends c tensor (b tensor x) to cb tensor x, which equals c tensor (b*x). For a target
identity, it is the multiplication unit at the extended object. Both paths for three
extensions send d tensor (c tensor (b tensor x)) to d*k(c)*k(j(b)) tensor x.
Associativity in the final completed coefficient ring proves equality, and local tensor
generation extends it to sheaves. Derived localization preserves these equations.
Expand the completed comparisons as conjugates by the normalized quotient-completion
maps; naturality moves intermediate comparisons past tensor maps and cancels adjacent
inverse factors, leaving the ordinary equations. Full-subcategory faithfulness and
rationalization preserve them. These arguments also cover identity embeddings and
E=L=M, the zero object, and the empty scheme. -/
theorem sfRationalScalar_coherence :
    (∀ K : sfRationalConstructibleCategory l E Y,
      (sfRationalScalarComp l E E (AlgHom.id (Padic l) E) Y p hl L ι).hom.app K =
        (sfRationalScalarExtension l E Y p hl L ι).map
          ((sfRationalScalarUnit l E Y p hl).hom.app K)) ∧
    (∀ K : sfRationalConstructibleCategory l E Y,
      (sfRationalScalarComp l E L ι Y p hl L (AlgHom.id (Padic l) L)).hom.app K =
        (sfRationalScalarUnit l L Y p hl).hom.app
          ((sfRationalScalarExtension l E Y p hl L ι).obj K)) ∧
    (∀ (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
      (k : M →ₐ[Padic l] N) (K : sfRationalConstructibleCategory l E Y),
      (sfRationalScalarExtension l M Y p hl N k).map
          ((sfRationalScalarComp l E L ι Y p hl M j).hom.app K) ≫
        (sfRationalScalarComp l E M (j.comp ι) Y p hl N k).hom.app K =
      (sfRationalScalarComp l L M j Y p hl N k).hom.app
          ((sfRationalScalarExtension l E Y p hl L ι).obj K) ≫
        (sfRationalScalarComp l E L ι Y p hl N (k.comp j)).hom.app K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K
    have ha := rational_comp_component l E E (AlgHom.id (Padic l) E) Y p hl L ι K
    have hb := map_heq (sfRationalScalarExtension l E Y p hl L ι)
      (rational_obj l E E (AlgHom.id (Padic l) E) Y p hl K) rfl
      (rational_unit_component l E Y p hl K)
    have hc := rational_map_localization l E L ι Y p hl
      ((sfIntegralScalarUnit l E Y p hl).hom.app K.obj)
    have hd := congrArg (fun f ↦ (sfRationalConstructibleLocalization l L Y).map f)
      (integral_source_unit l E L ι Y p hl K.obj)
    exact eq_of_heq (ha.trans ((heq_of_eq hd).trans (hb.trans hc).symm))
  · intro K
    have ha := rational_comp_component l E L ι Y p hl L (AlgHom.id (Padic l) L) K
    have hb' : HEq
        ((sfRationalScalarUnit l L Y p hl).hom.app
          ((sfRationalScalarExtension l E Y p hl L ι).obj K))
        ((sfRationalConstructibleLocalization l L Y).map
          ((sfIntegralScalarUnit l L Y p hl).hom.app
            ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K.obj))) := by
      exact (app_heq (sfRationalScalarUnit l L Y p hl).hom
        (rational_obj l E L ι Y p hl K)).trans
        (rational_unit_component l L Y p hl
          ⟨(sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K.obj⟩)
    have hd := congrArg (fun f ↦ (sfRationalConstructibleLocalization l L Y).map f)
      (integral_target_unit l E L ι Y p hl K.obj)
    exact eq_of_heq (ha.trans ((heq_of_eq hd).trans hb'.symm))
  · intro N _ _ _ k K
    have ha := map_heq (sfRationalScalarExtension l M Y p hl N k)
      (rational_obj_comp l E L ι Y p hl M j K)
      (rational_obj l E M (j.comp ι) Y p hl K)
      (rational_comp_component l E L ι Y p hl M j K)
    have ha' := rational_map_localization l M N k Y p hl
      ((sfIntegralScalarComp l E L ι Y p hl M j).hom.app K.obj)
    have hb := rational_comp_component l E M (j.comp ι) Y p hl N k K
    have hleft := comp_heq
      (by simp only [Functor.comp_obj, rational_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [rational_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [rational_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization]) (ha.trans ha') hb
    have hc' : HEq
        ((sfRationalScalarComp l L M j Y p hl N k).hom.app
          ((sfRationalScalarExtension l E Y p hl L ι).obj K))
        ((sfRationalConstructibleLocalization l N Y).map
          ((sfIntegralScalarComp l L M j Y p hl N k).hom.app
            ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K.obj))) := by
      exact (app_heq (sfRationalScalarComp l L M j Y p hl N k).hom
        (rational_obj l E L ι Y p hl K)).trans
        (rational_comp_component l L M j Y p hl N k
          ⟨(sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K.obj⟩)
    have hd := rational_comp_component l E L ι Y p hl N (k.comp j) K
    have hright := comp_heq
      (by simp only [Functor.comp_obj, rational_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [rational_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization])
      (by simp only [rational_obj,
        sfRationalConstructibleLocalization, ScalarLocalization.localization]) hc' hd
    have hi := congrArg (fun f ↦ (sfRationalConstructibleLocalization l N Y).map f)
      (integral_pentagon l E L ι Y p hl M j N k K.obj)
    rw [Functor.map_comp, Functor.map_comp] at hi
    exact eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

end WeilConjectures
