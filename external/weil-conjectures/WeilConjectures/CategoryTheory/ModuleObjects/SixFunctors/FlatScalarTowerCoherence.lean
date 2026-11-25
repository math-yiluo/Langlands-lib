/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option linter.privateModule false

/-!
# Coherence of exact scalar extension for sheaf module objects

Source: blueprint main-20261015, `lemma-descent-finite-coefficient-field`, proof (4) and the final
cocone paragraph; Stacks Tag 03CZ (blueprint: lem-sfb-flat-scalar-tower-coherence).

The comparisons are the existing `Mod.extendScalarsComp` (in the inverse orientation)
and `Mod.extendScalarsId`. The derived comparisons below apply the existing exact-functor
localization construction to these specified maps. The predicates package the clauses
without choosing a second tensor product or a second extension functor.
-/

@[expose] public section

universe u v uS vS w wA wB wC wR

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.Mod

section Ambient

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

end Ambient

section Derived

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {A B C : H} [MonObj A] [MonObj B] [MonObj C]
  [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
  [Abelian (Mod H A)] [Abelian (Mod H B)] [Abelian (Mod H C)]
  [HasDerivedCategory.{wA} (Mod H A)] [HasDerivedCategory.{wB} (Mod H B)]
  [HasDerivedCategory.{wC} (Mod H C)]
  (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]
  [(extendScalars f).Additive] [(extendScalars g).Additive]
  [(extendScalars (f ≫ g)).Additive]
  [PreservesFiniteLimits (extendScalars f)] [PreservesFiniteColimits (extendScalars f)]
  [PreservesFiniteLimits (extendScalars g)] [PreservesFiniteColimits (extendScalars g)]
  [PreservesFiniteLimits (extendScalars (f ≫ g))]
  [PreservesFiniteColimits (extendScalars (f ≫ g))]

end Derived

section DerivedUnit

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : H) [MonObj A] [IsCommMonObj A] [Abelian (Mod H A)]
  [HasDerivedCategory.{wA} (Mod H A)]
  [(extendScalars (𝟙 A)).Additive]
  [PreservesFiniteLimits (extendScalars (𝟙 A))]
  [PreservesFiniteColimits (extendScalars (𝟙 A))]

end DerivedUnit

section DerivedLaws

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

end DerivedLaws

section OrdinaryProof

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {A B C : H} [MonObj A] [MonObj B] [MonObj C]
  [IsCommMonObj A] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
omit [IsCommMonObj B] in
@[reassoc]
private theorem unit_naturality {M N : Mod H A} (p : M ⟶ N) :
    extendUnitHom f M ≫ ((extendScalars f).map p).hom =
      p.hom ≫ extendUnitHom f N := by
  have h := congrArg Hom.hom ((extendRestrictAdjunction f).unit.naturality p)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, extendRestrictAdjunction,
    Adjunction.mkOfHomEquiv_unit_app, extendHomEquiv, Equiv.coe_fn_mk, comp_hom',
    extendUnit_hom, comap_map_hom, id_hom', Functor.comp_map, extendScalars_map,
    Category.assoc] at h
  change p.hom ≫ extendUnitHom f N ≫ 𝟙 _ =
    extendUnitHom f M ≫ 𝟙 _ ≫ ((extendScalars f).map p).hom at h
  simpa only [Category.id_comp, Category.comp_id] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
omit [IsCommMonObj B] in
private theorem unit_transport {f' : A ⟶ B} [IsMonHom f'] (e : f = f') (M : Mod H A)
    (eM : (extendScalars f).obj M = (extendScalars f').obj M) :
    extendUnitHom f M ≫ (eqToHom eM).hom = extendUnitHom f' M := by
  subst f'
  simp only [eqToHom_refl, id_hom']
  exact Category.comp_id _

end OrdinaryProof

section DerivedProof

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {D₀ D₁ D₂ D₃ : Type*}
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂) (H : D₂ ⥤ D₃)
  (U : D₀ ⥤ D₂) (V : D₁ ⥤ D₃) (T : D₀ ⥤ D₃)
  [F.Additive] [G.Additive] [H.Additive] [U.Additive] [V.Additive] [T.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

end DerivedProof

section DerivedUnitProof

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
  [HasDerivedCategory D] [HasDerivedCategory E]
  (F T : D ⥤ E) [F.Additive] [T.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
private theorem derive_right_unit (U : E ⥤ E) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : U ≅ 𝟭 E) (a : T ≅ F ⋙ U) (hT : T = F)
    (ha : ∀ X, a.inv.app X ≫ eqToHom (congrArg (fun L ↦ L.obj X) hT) =
      e.hom.app (F.obj X)) (K : DerivedCategory D) :
    (Functor.mapDerivedCategoryTriangleIso a).inv.app K ≫
        eqToHom (by subst T; rfl) =
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso E).hom.app
        (F.mapDerivedCategory.obj K) := by
  subst T
  have heq : a.symm = Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    simpa only [Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, eqToHom_refl, Functor.id_obj,
      Functor.comp_obj, Category.comp_id] using ha X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hh := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app K) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans, hi, Category.comp_id] at hh
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hn hu
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv, NatTrans.comp_app,
    ← Functor.mapDerivedCategoryNatIso_symm, hh, Iso.trans_hom,
    eqToHom_refl, Category.comp_id]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F U).inv.app K), Iso.symm_inv,
    Iso.inv_hom_id_app_assoc, ← reassoc_of% hn, hu]
  exact (Category.comp_id _).symm

end DerivedUnitProof

section ScalarDerivedProof

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

end ScalarDerivedProof

end CategoryTheory.Mod
