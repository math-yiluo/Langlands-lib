/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
public import WeilConjectures.Topology.ProfiniteCondensedRing
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Section realization of the actual internal direct-image pairing

Source: Stacks Project, Modules on Sites, Tags 03D6, 03D7 and 03EK
(auxiliary; not a blueprint node).

All functors, adjunctions, balancing projections and pure-tensor comparisons below
are the existing specified constructions. Evaluation is used only after the canonical
pure-tensor map into a sheaf tensor, never as a tensor-preserving functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem unit_via_iso_three {C : Type*} [Category C] (F : C ⥤ C)
    (η : 𝟭 C ⟶ F) {A B B₁ B₂ : C} (e : B ≅ A)
    (α : B ⟶ B₁) (β : B₁ ⟶ B₂) (γ : B₂ ⟶ F.obj B)
    (h : α ≫ β ≫ γ = η.app B) :
    η.app A = e.inv ≫ α ≫ β ≫ γ ≫ F.map e.hom := by
  have hn := η.naturality e.hom
  have he : η.app A = e.inv ≫ η.app B ≫ F.map e.hom := by
    simpa only [Functor.id_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
      congrArg (fun k ↦ e.inv ≫ k) hn
  rw [he, ← h]
  simp only [Category.assoc]

private theorem regular_restrict_apply {R S : Type u} [CommRing R] [CommRing S]
    (c : R →+* S)
    (g : ModuleCat.of R R ⟶ (ModuleCat.restrictScalars c).obj (ModuleCat.of S S))
    (h : (show S from g 1) = 1) (r : R) : (show S from g r) = c r := by
  have hr := g.hom.map_smul r (1 : R)
  change (show S from g (r * 1)) = c r * (show S from g 1) at hr
  simpa only [mul_one, h] using hr

private theorem sectionTensor_natural (X : Scheme.{u})
    {M M' N N' : modules Λ X} (g : M ⟶ M') (h : N ⟶ N') (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    ((g ⊗ₘ h).val.app U) (sectionPureTensor Λ X M N U x y) =
      sectionPureTensor Λ X M' N' U ((g.val.app U) x) ((h.val.app U) y) :=
  InternalAbelianSheafModule.comparison_sectionTmul_natural
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) g h U x y

private theorem tensorComparison_apply (X : Scheme.{u}) (M N : internalModules Λ X)
    (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((ordinaryTensorComparison Λ X M N).hom.val.app U)
        (internalPureTensor Λ X M N U x y) =
      sectionPureTensor Λ X ((equivalence Λ X).functor.obj M)
        ((equivalence Λ X).functor.obj N) U x y :=
  (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec U x y

private theorem unitComparison_apply (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (r : (condensedRingObj Λ X).obj.obj U) :
    ((ordinaryUnitComparison Λ X).hom.val.app U) r = r :=
  (ordinaryUnitComparison_existsUnique Λ X).exists.choose_spec U r

private theorem internalSectionTensor_hom_ext (X : Scheme.{u})
    (M N : internalModules Λ X) (H : modules Λ X)
    {g h : (equivalence Λ X).functor.obj (M ⊗ N) ⟶ H}
    (he : ∀ (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      (g.val.app U) (internalPureTensor Λ X M N U x y) =
        (h.val.app U) (internalPureTensor Λ X M N U x y)) : g = h := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply (cancel_epi (Mod.tensorObjπ M N)).mp
  apply Sheaf.tensor_hom_ext
  ext U t
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul x y => exact he U x y

private theorem pushComparison_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : internalModules Λ X) (U : Y.ProEtᵒᵖ) (x : M.X.obj.obj
      ((InternalModuleOperations.siteMap f).op.obj U)) :
    (((pushComparison Λ f).hom.app M).val.app U) x = x :=
  (InternalModuleOperations.lowerComparison_existsUnique Λ f).exists.choose_spec M U x

section GenericInternalTensor
universe v w z
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
variable {C : Type w} [Category.{z} C] (J : GrothendieckTopology C)
  [UnivLE.{max w z, v}] [HasSheafify J Ab.{v}]
  [(J.W (A := Ab.{v})).IsMonoidal]
  (R : Sheaf J Ab.{v}) [MonObj R] [IsCommMonObj R]

private theorem genericInternalTensor_leftUnitor (M : Mod (Sheaf J Ab.{v}) R)
    (U : Cᵒᵖ) (r : (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U)
    (x : M.X.obj.obj U) :
    ((λ_ M).hom.hom.hom.app U)
        (InternalAbelianSheafModule.comparison_internalTmul J R (𝟙_ _) M U r x) =
      (r • (show ((InternalAbelianSheafModule.sectionModuleFunctor J R).obj M).val.obj U
        from x)) :=
  InternalAbelianSheafModule.comparison_internalTmul_leftUnitor J R M U r x

private theorem genericInternalTensor_natural
    {M M' N N' : Mod (Sheaf J Ab.{v}) R} (g : M ⟶ M') (h : N ⟶ N') (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((g ⊗ₘ h).hom.hom.app U) (InternalAbelianSheafModule.comparison_internalTmul J R M N U x y) =
      InternalAbelianSheafModule.comparison_internalTmul J R M' N' U
        ((g.hom.hom.app U) x) ((h.hom.hom.app U) y) :=
  InternalAbelianSheafModule.comparison_internalTmul_natural J R g h U x y

end GenericInternalTensor

private theorem internalPush_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((CondensedRing.lowerStar Λ f).obj M).X.obj.obj U)
    (y : ((CondensedRing.lowerStar Λ f).obj N).X.obj.obj U) :
    (((internalPushLax Λ f).μ M N).hom.hom.app U)
        (internalPureTensor Λ Y _ _ U x y) =
      internalPureTensor Λ X M N ((InternalModuleOperations.siteMap f).op.obj U) x y :=
  (internalPushNormalized_existsUnique Λ f).exists.choose_spec M N U x y

private theorem push_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : modules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((pushforward Λ f).obj M).val.obj U)
    (y : ((pushforward Λ f).obj N).val.obj U) :
    (((pushLax Λ f).μ M N).val.app U) (sectionPureTensor Λ Y _ _ U x y) =
      sectionPureTensor Λ X M N ((InternalModuleOperations.siteMap f).op.obj U) x y :=
  (pushNormalized_existsUnique Λ f).exists.choose_spec M N U x y

attribute [local irreducible]
  InternalAbelianSheafModule.comparison_sectionTmul
  InternalAbelianSheafModule.comparison_internalTmul
  ordinaryTensorComparison ordinaryUnitComparison internalPushLax pushLax
  InternalModuleOperations.lowerComparison InternalModuleOperations.upperComparison

section GenericSectionPushUnit
universe v uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [EssentiallySmall.{v} C] [EssentiallySmall.{v} D]
  (R : Sheaf J CommRingCat.{v}) (S : Sheaf K CommRingCat.{v})

private theorem genericSectionPush_unit (F : C ⥤ D) [F.IsContinuous J K]
    (c : (sheafCompose J (forget₂ CommRingCat.{v} RingCat.{v})).obj R ⟶
      (F.sheafPushforwardContinuous RingCat.{v} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{v} RingCat.{v})).obj S))
    (m : (SheafOfModules.pushforward.{v} c).LaxMonoidal)
    (hm : SheafOfModules.RingedPushforwardPureTensor F R S c m)
    (U : Cᵒᵖ) (r : R.obj.obj U) :
    m.ε.val.app U r = c.hom.app U r := by
  obtain ⟨n, _, he, hu⟩ :=
    SheafOfModules.exists_unique_ringedPushforward_laxMonoidal F R S c
  exact (congrArg (fun k : (SheafOfModules.pushforward c).LaxMonoidal ↦
    k.ε.val.app U r) (hu m hm)).trans (he U r)

end GenericSectionPushUnit

private theorem push_unit_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj U) :
    ((pushLax Λ f).ε.val.app U) r = ((coefficientMap Λ f).hom.app U) r := by
  let := InternalModuleOperations.siteMap_continuous f
  apply genericSectionPush_unit (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (ring Λ Y) (ring Λ X) (InternalModuleOperations.siteMap f)
    (coefficientMap Λ f) (pushLax Λ f) ?_ U r
  intro M N V x y
  have h := push_apply Λ f M N V x y
  unfold sectionPureTensor InternalAbelianSheafModule.comparison_sectionTmul at h
  exact h

-- Internal scalar restriction introduces large coefficient types.
private theorem internalPush_unit_composite_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj U) :
    (((equivalence Λ Y).functor.map (internalPushLax Λ f).ε ≫
      (pushComparison Λ f).hom.app (𝟙_ (internalModules Λ X)) ≫
      (pushforward Λ f).map (ordinaryUnitComparison Λ X).hom).val.app U) r =
        ((coefficientMap Λ f).hom.app U) r := by
  let F := CondensedRing.lowerStar Λ f
  let I := 𝟙_ (internalModules Λ X)
  let e := (internalPushLax Λ f).ε
  have h := Functor.LaxMonoidal.left_unitality F I
  rw [← MonoidalCategory.tensorHom_id] at h
  have he := congrArg (fun k ↦ (k.hom.hom.app U)
    (internalPureTensor Λ Y (𝟙_ _) (F.obj I) U
      (1 : (ring Λ Y).obj.obj U)
      (1 : (ring Λ X).obj.obj ((InternalModuleOperations.siteMap f).op.obj U)))) h
  change ((λ_ (F.obj I)).hom.hom.hom.app U) _ =
    (((λ_ I).hom.hom.hom.app ((InternalModuleOperations.siteMap f).op.obj U)))
      ((((internalPushLax Λ f).μ I I).hom.hom.app U)
        (((e ⊗ₘ 𝟙 (F.obj I)).hom.hom.app U) _)) at he
  rw [genericInternalTensor_leftUnitor, one_smul, genericInternalTensor_natural,
    internalPush_apply,
    genericInternalTensor_leftUnitor] at he
  change (1 : (ring Λ X).obj.obj ((InternalModuleOperations.siteMap f).op.obj U)) =
    (show (ring Λ X).obj.obj ((InternalModuleOperations.siteMap f).op.obj U) from
      (e.hom.hom.app U) (1 : (ring Λ Y).obj.obj U)) * 1 at he
  rw [mul_one] at he
  let es := (equivalence Λ Y).functor.map e ≫
    (pushComparison Λ f).hom.app I ≫ (pushforward Λ f).map (ordinaryUnitComparison Λ X).hom
  have hes (t : (ring Λ Y).obj.obj U) :
      (es.val.app U) t = (e.hom.hom.app U) t := by
    change ((ordinaryUnitComparison Λ X).hom.val.app
      ((InternalModuleOperations.siteMap f).op.obj U))
        ((((pushComparison Λ f).hom.app I).val.app U) ((e.hom.hom.app U) t)) = _
    exact (congrArg ((ordinaryUnitComparison Λ X).hom.val.app
        ((InternalModuleOperations.siteMap f).op.obj U))
      (pushComparison_apply Λ f I U ((e.hom.hom.app U) t))).trans
        (unitComparison_apply Λ X _ _)
  exact regular_restrict_apply (R := (ring Λ Y).obj.obj U)
    (S := (ring Λ X).obj.obj ((InternalModuleOperations.siteMap f).op.obj U))
    (((coefficientMap Λ f).hom.app U).hom) (es.val.app U)
    ((hes 1).trans he.symm) r

private theorem projection_pairing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ X) :
    Mod.tensorObjπ ((CondensedRing.lowerStar Λ f).obj M)
        ((CondensedRing.lowerStar Λ f).obj N) ≫
      ((internalPushLax Λ f).μ M N).hom =
    Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) := by
  apply Sheaf.tensor_hom_ext
  ext U t
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul x y =>
    have hn := internalPush_apply Λ f M N U x y
    unfold internalPureTensor InternalAbelianSheafModule.comparison_internalTmul at hn
    have hc := NatTrans.IsMonoidal.tensor
      (τ := (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
        (InternalModuleOperations.siteMap f) Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).hom) M.X N.X
    simp only [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
      id_tensorHom_id, Category.id_comp, Category.comp_id, Functor.LaxMonoidal.comp_μ] at hc
    have hU := congrArg (fun k ↦ (k.app U) (x ⊗ₜ[ℤ] y)) hc
    change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      M.X N.X).app ((InternalModuleOperations.siteMap f).op.obj U)) (x ⊗ₜ[ℤ] y) =
      ((Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X).hom.app U)
        (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          ((CondensedRing.lowerStar Λ f).obj M).X
          ((CondensedRing.lowerStar Λ f).obj N).X).app U) (x ⊗ₜ[ℤ] y)) at hU
    exact hn.trans (congrArg (fun z ↦
      (((ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N)).hom.app U) z) hU)

-- The two specified adjunctions involve large coefficient types.
-- Comparisons of reconstructed module structures involve large coefficient types.
/-- The fixed section comparisons identify the actual adjunction and lax direct image.
Source: Stacks Project, Modules on Sites, Tags 03D6, 03D7 and 03EK
(auxiliary; not a blueprint node).

Proof:
1. The existing internal-module operations transport theorem gives the mate equation
   and the unit and counit equations for the specified comparisons.
2. The internal pairing normalization gives its value on local pure tensors. The
   monoidality of the sheaf-to-presheaf pushforward comparison identifies the abelian
   pairing on the same generators. Cancel the relative-tensor projection and use
   tensor induction to obtain the balancing-projection equation.
3. The ordinary tensor comparisons fix pure tensors, and the direct-image comparison
   fixes sections. Naturality of section pure tensors follows from the tensorator of
   the module-sheafification right adjoint. These facts and the two pushforward
   normalizations identify both composites of the tensor comparison square.
4. Ringed direct-image lax uniqueness gives the section unit formula. Internal lax
   left-unitality at the regular module, evaluated on 1 tensor 1, gives that the
   internal unit sends 1 to 1. The reconstructed composite is linear over R_Y,
   so it sends r to c(r). The ordinary unit comparisons fix sections, proving
   the unit comparison square. The section pairing formula is its normalization.
5. Naturality transports the adjunction unit along the equivalence counit from
   the internal inverse image of any section module. The internal adjunction Hom
   formula at the identity is geometric insertion followed by extendUnitHom.
   Evaluating the transported equation and using the direct-image comparison's
   section formula yields the required arbitrary-module unit formula.
-/
theorem internal_direct_image_lax_realization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
      (.mk _ _ _ _ (pullComparison Λ f).inv)) = (pushComparison Λ f).hom ∧
    (∀ M : internalModules Λ Y,
      (equivalence Λ Y).functor.map
          ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M) ≫
        (pushComparison Λ f).hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
        (pushforward Λ f).map ((pullComparison Λ f).hom.app M) =
      (adjunction Λ f).unit.app ((equivalence Λ Y).functor.obj M)) ∧
    (∀ N : internalModules Λ X,
      (pullback Λ f).map ((pushComparison Λ f).inv.app N) ≫
        (pullComparison Λ f).inv.app ((CondensedRing.lowerStar Λ f).obj N) ≫
        (equivalence Λ X).functor.map
          ((CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app N) =
      (adjunction Λ f).counit.app ((equivalence Λ X).functor.obj N)) ∧
    (∀ M N : internalModules Λ X,
      Mod.tensorObjπ ((CondensedRing.lowerStar Λ f).obj M)
          ((CondensedRing.lowerStar Λ f).obj N) ≫
        ((internalPushLax Λ f).μ M N).hom =
      Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N)) ∧
    (∀ M N : internalModules Λ X,
      (ordinaryTensorComparison Λ Y
          ((CondensedRing.lowerStar Λ f).obj M) ((CondensedRing.lowerStar Λ f).obj N)).hom ≫
        ((pushComparison Λ f).hom.app M ⊗ₘ (pushComparison Λ f).hom.app N) ≫
        (pushLax Λ f).μ ((equivalence Λ X).functor.obj M)
          ((equivalence Λ X).functor.obj N) =
      (equivalence Λ Y).functor.map ((internalPushLax Λ f).μ M N) ≫
        (pushComparison Λ f).hom.app (M ⊗ N) ≫
        (pushforward Λ f).map (ordinaryTensorComparison Λ X M N).hom) ∧
    ((equivalence Λ Y).functor.map (internalPushLax Λ f).ε ≫
        (pushComparison Λ f).hom.app (𝟙_ (internalModules Λ X)) ≫
        (pushforward Λ f).map (ordinaryUnitComparison Λ X).hom =
      (ordinaryUnitComparison Λ Y).hom ≫ (pushLax Λ f).ε) ∧
    (∀ (H K : modules Λ X) (V : Y.ProEtᵒᵖ)
        (a : ((pushforward Λ f).obj H).val.obj V)
        (b : ((pushforward Λ f).obj K).val.obj V),
      (((pushLax Λ f).μ H K).val.app V) (sectionPureTensor Λ Y _ _ V a b) =
        sectionPureTensor Λ X H K ((InternalModuleOperations.siteMap f).op.obj V) a b) ∧
    (∀ (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V),
      ((pushLax Λ f).ε.val.app V) r = ((coefficientMap Λ f).hom.app V) r) ∧
    (∀ (A : modules Λ Y) (V : Y.ProEtᵒᵖ) (a : A.val.obj V),
      (((adjunction Λ f).unit.app A).val.app V) a =
        ((((pullback Λ f).map ((equivalence Λ Y).counitIso.hom.app A)).val.app
            ((InternalModuleOperations.siteMap f).op.obj V)))
          ((((pullComparison Λ f).hom.app ((equivalence Λ Y).inverse.obj A)).val.app
              ((InternalModuleOperations.siteMap f).op.obj V))
            (((Mod.extendUnitHom (condensedPullbackHom Λ f)
                (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj
                  ((equivalence Λ Y).inverse.obj A))).hom.app
                ((InternalModuleOperations.siteMap f).op.obj V))
              ((((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app
                  ((equivalence Λ Y).inverse.obj A).X).hom.app V)
                ((((equivalence Λ Y).counitIso.inv.app A).val.app V) a))))) := by
  have ht := (InternalModuleOperations.internal_module_operations_transport Λ).2.1 f
  have hu := ht.2.1
  refine ⟨ht.1, hu, ht.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact projection_pairing Λ f
  · intro M N
    apply internalSectionTensor_hom_ext Λ Y
    intro U x y
    change (((pushLax Λ f).μ _ _).val.app U)
        (((((pushComparison Λ f).hom.app M ⊗ₘ
          (pushComparison Λ f).hom.app N)).val.app U)
          (((ordinaryTensorComparison Λ Y _ _).hom.val.app U)
            (internalPureTensor Λ Y _ _ U x y))) =
      (((ordinaryTensorComparison Λ X M N).hom.val.app
        ((InternalModuleOperations.siteMap f).op.obj U)))
        ((((pushComparison Λ f).hom.app (M ⊗ N)).val.app U)
          ((((internalPushLax Λ f).μ M N).hom.hom.app U)
            (internalPureTensor Λ Y _ _ U x y)))
    let MY := (CondensedRing.lowerStar Λ f).obj M
    let NY := (CondensedRing.lowerStar Λ f).obj N
    let EX := (equivalence Λ X).functor
    let EY := (equivalence Λ Y).functor
    let W := (InternalModuleOperations.siteMap f).op.obj U
    let g := (pushComparison Λ f).hom.app M
    let h := (pushComparison Λ f).hom.app N
    let p := ((pushLax Λ f).μ (EX.obj M) (EX.obj N)).val.app U
    let q := (ordinaryTensorComparison Λ X M N).hom.val.app W
    have ht := congrArg
      (fun z : (EY.obj MY ⊗ EY.obj NY).val.obj U ↦ p (((g ⊗ₘ h).val.app U) z))
      (tensorComparison_apply Λ Y MY NY U x y)
    have hn := congrArg (fun z ↦ p z) (sectionTensor_natural Λ Y g h U x y)
    have hg := pushComparison_apply Λ f M U x
    have hh := pushComparison_apply Λ f N U y
    have hp := push_apply Λ f (EX.obj M) (EX.obj N) U x y
    have hi := internalPush_apply Λ f M N U x y
    have hc := pushComparison_apply Λ f (M ⊗ N) U
      ((((internalPushLax Λ f).μ M N).hom.hom.app U)
        (internalPureTensor Λ Y MY NY U x y))
    have hq := tensorComparison_apply Λ X M N W x y
    have hleft : p (sectionPureTensor Λ Y _ _ U ((g.val.app U) x)
        ((h.val.app U) y)) = sectionPureTensor Λ X (EX.obj M) (EX.obj N) W x y := by
      exact (congrArg (fun z ↦ p z) (congrArg₂
        (fun a b ↦ sectionPureTensor Λ Y
          ((pushforward Λ f).obj (EX.obj M)) ((pushforward Λ f).obj (EX.obj N)) U a b)
        hg hh)).trans hp
    exact ht.trans (hn.trans (hleft.trans
      ((congrArg (fun z ↦ q z) (hc.trans hi)).trans hq).symm))
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have hr := (congrArg (fun z ↦ ((pushLax Λ f).ε.val.app U) z)
      (unitComparison_apply Λ Y U r)).trans (push_unit_apply Λ f U r)
    exact (internalPush_unit_composite_apply Λ f U r).trans hr.symm
  · exact push_apply Λ f
  · exact push_unit_apply Λ f
  · intro A V a
    let M := (equivalence Λ Y).inverse.obj A
    have he := unit_via_iso_three (pullback Λ f ⋙ pushforward Λ f)
      (adjunction Λ f).unit ((equivalence Λ Y).counitIso.app A)
      ((equivalence Λ Y).functor.map
        ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M))
      ((pushComparison Λ f).hom.app ((CondensedRing.upperStar Λ f).obj M))
      ((pushforward Λ f).map ((pullComparison Λ f).hom.app M)) (hu M)
    have hi := CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom Λ f M
      ((CondensedRing.upperStar Λ f).obj M) (𝟙 _)
    rw [Adjunction.homEquiv_id] at hi
    change ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          (Mod.extendUnitHom (condensedPullbackHom Λ f)
            (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M) ≫
              𝟙 _) at hi
    rw [Category.comp_id] at hi
    have heV := congrArg (fun k : A ⟶ (pushforward Λ f).obj ((pullback Λ f).obj A) ↦
      (k.val.app V) a) he
    apply heV.trans
    change (((pullback Λ f).map ((equivalence Λ Y).counitIso.hom.app A)).val.app
      ((InternalModuleOperations.siteMap f).op.obj V))
        ((((pullComparison Λ f).hom.app M).val.app
          ((InternalModuleOperations.siteMap f).op.obj V))
          ((((pushComparison Λ f).hom.app _).val.app V)
            ((((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom.hom.app V)
              ((((equivalence Λ Y).counitIso.inv.app A).val.app V) a)))) = _
    have hp := pushComparison_apply Λ f ((CondensedRing.upperStar Λ f).obj M) V
      ((((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom.hom.app V)
        ((((equivalence Λ Y).counitIso.inv.app A).val.app V) a))
    have hiV := congrArg (fun k ↦ (k.hom.app V)
      ((((equivalence Λ Y).counitIso.inv.app A).val.app V) a)) hi
    exact congrArg (fun z : ((CondensedRing.upperStar Λ f).obj M).X.obj.obj
        ((InternalModuleOperations.siteMap f).op.obj V) ↦
      (((pullback Λ f).map ((equivalence Λ Y).counitIso.hom.app A)).val.app
        ((InternalModuleOperations.siteMap f).op.obj V))
        ((((pullComparison Λ f).hom.app M).val.app
          ((InternalModuleOperations.siteMap f).op.obj V)) z)) (hp.trans hiV)

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
