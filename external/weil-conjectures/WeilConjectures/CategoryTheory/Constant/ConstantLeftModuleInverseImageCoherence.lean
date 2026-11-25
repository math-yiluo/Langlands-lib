/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-! Coherence comparisons for constant left-module inverse images.
Source: Stacks Project, Sites, Tags 00YV and 00XZ (blueprint:
lem-pe-constant-left-module-inverse-image).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
open ConstantLeftModuleInverseImage
attribute [local instance] comp_preservesFiniteLimits

set_option backward.isDefEq.respectTransparency false in
private def scalarEndomorphism
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J Λ) (r : Λ) : (V J Λ).obj M ⟶ (V J Λ).obj M where
  hom :=
    { app := fun T ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦
            ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x
          map_zero' := smul_zero _
          map_add' := smul_add _ }
      naturality := by
        intro T S f
        ext x
        change M.val.obj T at x
        change
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app S r) •
              M.val.map f x =
            M.val.map f
              (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x)
        rw [M.val.map_smul]
        congr 1
        exact congrArg (fun g ↦ g r)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).naturality f) }

private theorem scalarEndomorphism_isScalar
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J Λ) (r : Λ) :
    IsScalar J Λ M r (scalarEndomorphism J Λ M r) := by
  intro T x
  rfl

private def linearHomOfConstantScalars
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    {M N : Modules J Λ} (f : (V J Λ).obj M ⟶ (V J Λ).obj N)
    (hf : ∀ r : Λ,
      scalarEndomorphism J Λ M r ≫ f = f ≫ scalarEndomorphism J Λ N r) : M ⟶ N := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
      (PresheafOfModules.restrictScalars α).obj N.val :=
    PresheafOfModules.homMk f.hom (by
      intro T r x
      exact congrArg (fun k ↦ k.hom.app T x) (hf r))
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    α N.isSheaf).symm g⟩

private def abelianLift
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) : F ⟶ G := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact (H.preimage (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G)
    (ObjectProperty.homMk α)).hom

private theorem abelianLift_forget
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) :
    Functor.whiskerRight (abelianLift F G α) (forget AddCommGrpCat) = α := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact congrArg (fun f ↦ f.hom) (H.map_preimage
    (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G) (ObjectProperty.homMk α))

private theorem linearHomOfConstantScalars_forget
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    {M N : Modules J Λ} (f : (V J Λ).obj M ⟶ (V J Λ).obj N)
    (hf : ∀ r : Λ,
      scalarEndomorphism J Λ M r ≫ f = f ≫ scalarEndomorphism J Λ N r) :
    (V J Λ).map (linearHomOfConstantScalars J Λ f hf) = f := by
  rfl

private theorem moduleNatTrans
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (F G : Modules J Λ ⥤ Modules K Λ)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ W K Λ ⟶ G ⋙ W K Λ)
    (hα : ∀ (M : Modules J Λ) (r : Λ),
      (U K).map (scalarEndomorphism K Λ (F.obj M) r) ≫ α.app M =
        α.app M ≫ (U K).map (scalarEndomorphism K Λ (G.obj M) r)) :
    ∃ a : F ⟶ G, Functor.whiskerRight a (W K Λ) = α := by
  let : HasFiniteBiproducts (Modules J Λ) := .of_hasFiniteProducts
  have : PreservesFiniteLimits (V K Λ) := inferInstance
  have : PreservesFiniteLimits (sheafToPresheaf K AddCommGrpCat.{u}) := inferInstance
  have (T : Dᵒᵖ) :
      PreservesFiniteLimits ((evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      (F ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      (G ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  let b := fun T : Dᵒᵖ ↦ abelianLift
    (F ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    (G ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    { app := fun N ↦ (α.app N).hom.app T
      naturality := by
        intro M N f
        exact congrArg (fun k ↦ k.hom.app T) (α.naturality f) }
  have hb (T : Dᵒᵖ) (M : Modules J Λ) :
      (forget AddCommGrpCat).map ((b T).app M) = (α.app M).hom.app T := by
    dsimp only [b]
    exact congr_app (abelianLift_forget _ _ _) M
  let a : F ⋙ V K Λ ⟶ G ⋙ V K Λ :=
    { app := fun M ↦
        { hom :=
            { app := fun T ↦ (b T).app M
              naturality := by
                intro T S f
                apply (forget AddCommGrpCat).map_injective
                change (forget AddCommGrpCat).map (((F ⋙ V K Λ).obj M).obj.map f) ≫
                    (forget AddCommGrpCat).map ((b S).app M) =
                  (forget AddCommGrpCat).map ((b T).app M) ≫
                    (forget AddCommGrpCat).map (((G ⋙ V K Λ).obj M).obj.map f)
                rw [hb, hb]
                exact (α.app M).hom.naturality f } }
      naturality := by
        intro M N f
        ext T x
        exact congrArg (fun k ↦ k.hom x) ((b T).naturality f) }
  have ha (M : Modules J Λ) : (U K).map (a.app M) = α.app M := by
    ext T x
    exact congrArg (fun k ↦ k x) (hb T M)
  refine ⟨
    { app := fun M ↦ linearHomOfConstantScalars K Λ (a.app M) (fun r ↦ ?_)
      naturality := ?_ }, ?_⟩
  · apply (U K).map_injective
    simpa only [Functor.map_comp, ha] using hα M r
  · intro M N f
    apply (V K Λ).map_injective
    simpa only [Functor.map_comp, Functor.comp_map, linearHomOfConstantScalars_forget]
      using a.naturality f
  · ext M T x
    exact congrArg (fun k ↦ k.hom.app T x) (ha M)

private theorem liftScalarMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    (M : Modules J Λ) (r : Λ) :
    (U K).map (scalarEndomorphism K Λ (d.moduleFunctor.obj M) r) ≫
        d.moduleSetIso.hom.app M =
      d.moduleSetIso.hom.app M ≫ L.map ((U J).map (scalarEndomorphism J Λ M r)) := by
  have h := d.scalar_compatibility M r _ _
    (scalarEndomorphism_isScalar J Λ M r)
    (scalarEndomorphism_isScalar K Λ (d.moduleFunctor.obj M) r)
  rw [← d.moduleSetIso_compatibility]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg ((U K).map (d.underlyingIso.hom.app M) ≫ ·)
      (d.abelianSetIso.hom.naturality (scalarEndomorphism J Λ M r))

private theorem moduleIsoOfScalars
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (F G : Modules J Λ ⥤ Modules K Λ)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (e : F ⋙ W K Λ ≅ G ⋙ W K Λ)
    (he : ∀ (M : Modules J Λ) (r : Λ),
      (U K).map (scalarEndomorphism K Λ (F.obj M) r) ≫ e.hom.app M =
        e.hom.app M ≫ (U K).map (scalarEndomorphism K Λ (G.obj M) r)) :
    ∃ i : F ≅ G, Functor.whiskerRight i.hom (W K Λ) = e.hom := by
  obtain ⟨a, ha⟩ := moduleNatTrans J K Λ F G e.hom he
  have : IsIso (Functor.whiskerRight a (W K Λ)) := by rw [ha]; infer_instance
  have : IsIso (((Functor.whiskeringRight _ _ _).obj (W K Λ)).map a) := by
    change IsIso (Functor.whiskerRight a (W K Λ))
    infer_instance
  have : IsIso a := isIso_of_reflects_iso a ((Functor.whiskeringRight _ _ _).obj (W K Λ))
  exact ⟨asIso a, ha⟩

set_option backward.isDefEq.respectTransparency false in
private theorem compositionComparison
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (H : GrothendieckTopology E) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    [HasWeakSheafify H RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (L₂ : Sheaf K (Type u) ⥤ Sheaf H (Type u))
    (R₂ : Sheaf H (Type u) ⥤ Sheaf K (Type u))
    (adj₂ : L₂ ⊣ R₂) (hL₂ : PreservesFiniteLimits L₂)
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    (d₂ : ConstantLeftModuleInverseImageLift K H Λ L₂ R₂ adj₂ hL₂)
    (d₃ : ConstantLeftModuleInverseImageLift J H Λ (L ⋙ L₂) (R₂ ⋙ R)
      (adj.comp adj₂) (@comp_preservesFiniteLimits _ _ _ _ _ _ L L₂ hL hL₂)) :
    ∃ i : d₃.moduleFunctor ≅ d.moduleFunctor ⋙ d₂.moduleFunctor,
      ∀ M : Modules J Λ,
        (W H Λ).map (i.hom.app M) ≫ d₂.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
          L₂.map (d.moduleSetIso.hom.app M) = d₃.moduleSetIso.hom.app M := by
  let := d.preservesFiniteLimits
  let := d₂.preservesFiniteLimits
  let := d₃.preservesFiniteLimits
  let β : (d.moduleFunctor ⋙ d₂.moduleFunctor) ⋙ W H Λ ≅ W J Λ ⋙ (L ⋙ L₂) :=
    Functor.isoWhiskerLeft d.moduleFunctor d₂.moduleSetIso ≪≫
      Functor.isoWhiskerRight d.moduleSetIso L₂
  let α : d₃.moduleFunctor ⋙ W H Λ ≅ (d.moduleFunctor ⋙ d₂.moduleFunctor) ⋙ W H Λ :=
    d₃.moduleSetIso ≪≫ β.symm
  obtain ⟨i, hi⟩ := moduleIsoOfScalars J H Λ _ _ α (by
    intro M r
    apply (cancel_mono (β.hom.app M)).mp
    change _ ≫ ((d₃.moduleSetIso.hom.app M ≫ β.inv.app M) ≫ β.hom.app M) =
      (d₃.moduleSetIso.hom.app M ≫ β.inv.app M) ≫
        (U H).map (scalarEndomorphism H Λ
          (d₂.moduleFunctor.obj (d.moduleFunctor.obj M)) r) ≫ β.hom.app M
    simp only [Iso.inv_hom_id_app, Category.comp_id, Category.assoc]
    rw [liftScalarMap J H Λ (L ⋙ L₂) (R₂ ⋙ R) (adj.comp adj₂) _ d₃ M r]
    have hb : (U H).map (scalarEndomorphism H Λ
          (d₂.moduleFunctor.obj (d.moduleFunctor.obj M)) r) ≫ β.hom.app M =
        β.hom.app M ≫ L₂.map (L.map ((U J).map (scalarEndomorphism J Λ M r))) := by
      change _ ≫ (d₂.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
        L₂.map (d.moduleSetIso.hom.app M)) =
        (d₂.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
          L₂.map (d.moduleSetIso.hom.app M)) ≫ _
      rw [← Category.assoc, liftScalarMap K H Λ L₂ R₂ adj₂ hL₂ d₂
        (d.moduleFunctor.obj M) r, Category.assoc, ← L₂.map_comp,
        liftScalarMap J K Λ L R adj hL d M r, L₂.map_comp, Category.assoc]
    rw [hb]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rfl)
  refine ⟨i, fun M ↦ ?_⟩
  have h := congr_app hi M
  change (W H Λ).map (i.hom.app M) =
    d₃.moduleSetIso.hom.app M ≫ β.inv.app M at h
  change (W H Λ).map (i.hom.app M) ≫ β.hom.app M = _
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end CategoryTheory
