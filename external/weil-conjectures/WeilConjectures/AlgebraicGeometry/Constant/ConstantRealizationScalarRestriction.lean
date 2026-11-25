/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.AlgebraicGeometry.Constant.ConstantRealizationScalarRestrictionUnderlying

/-! # Constant realization and scalar restriction

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EL.
(blueprint: lem-weil-pbc-constant-realization-scalar-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
universe t uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem nonemptyIsoOfMappedComponents
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (T : D ⥤ E) [T.Faithful] {F G : C ⥤ D}
    (h : F ⋙ T = G ⋙ T)
    (hs : ∀ M, ∃ e : F.obj M ≅ G.obj M,
      T.map e.hom = (eqToHom h).app M) : Nonempty (F ≅ G) := by
  choose e he using hs
  refine ⟨NatIso.ofComponents e ?_⟩
  intro M N g
  apply T.map_injective
  rw [T.map_comp, T.map_comp, he, he]
  exact (eqToHom h).naturality g

private theorem sheafRestrictionForget
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{t + 1}} (f : R ⟶ S) :
    SheafOfModules.restrictScalars.{t + 1} f ⋙ SheafOfModules.toSheaf R =
      SheafOfModules.toSheaf S := rfl

private theorem moduleRestrictionForget {B D : Type t} [CommRing B] [CommRing D]
    (f : B →+* D) :
    ModuleCat.restrictScalars.{t} f ⋙ forget₂ (ModuleCat.{t} B) AddCommGrpCat.{t} =
      forget₂ (ModuleCat.{t} D) AddCommGrpCat.{t} := rfl

private theorem liftedModuleForget (B : Type t) [CommRing B] :
    ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
      forget₂ (ModuleCat.{t + 1} (ULift.{t + 1} B)) AddCommGrpCat.{t + 1} =
    forget₂ (ModuleCat.{t} B) AddCommGrpCat.{t} ⋙ AddCommGrpCat.uliftFunctor.{t + 1} := rfl

private theorem constantPresheafForget
    {C : Type uC} [Category.{vC} C] (B : Type (max uC vC)) [CommRing B] :
    siteConstantModulePresheafGeneral (C := C) B ⋙ PresheafOfModules.toPresheaf _ =
      forget₂ (ModuleCat B) AddCommGrpCat ⋙ Functor.const Cᵒᵖ := rfl

private theorem sheafificationForget
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R₀ : Cᵒᵖ ⥤ RingCat.{t + 1}} {R : Sheaf J RingCat.{t + 1}}
    [HasWeakSheafify J AddCommGrpCat.{t + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective J α]
    [Presheaf.IsLocallySurjective J α] :
    PresheafOfModules.sheafification.{t + 1} α ⋙ SheafOfModules.toSheaf R =
      PresheafOfModules.toPresheaf R₀ ⋙ presheafToSheaf J AddCommGrpCat.{t + 1} := rfl

private theorem constantRealization_forget (X : Scheme.{t})
    (B : Type t) [CommRing B] :
    (ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
          koszulConstantFunctor X B) ⋙ SheafOfModules.toSheaf (adicModuleRing X B) =
    forget₂ (ModuleCat.{t} B) AddCommGrpCat.{t} ⋙ AddCommGrpCat.uliftFunctor.{t + 1} ⋙
      Functor.const X.ProEtᵒᵖ ⋙ presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1} := by
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  let L := ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  let P := siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} B)
  let a := presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}
  calc
    _ = L ⋙ P ⋙ PresheafOfModules.toPresheaf _ ⋙ a :=
      congrArg (fun F ↦ L ⋙ P ⋙ F) (sheafificationForget (koszulConstantUnit X B))
    _ = L ⋙ forget₂ (ModuleCat.{t + 1} (ULift.{t + 1} B)) AddCommGrpCat.{t + 1} ⋙
        Functor.const X.ProEtᵒᵖ ⋙ a :=
      congrArg (fun F ↦ L ⋙ F ⋙ a) (constantPresheafForget (C := X.ProEt) _)
    _ = _ := congrArg (fun F ↦ F ⋙ Functor.const X.ProEtᵒᵖ ⋙ a) (liftedModuleForget B)

private theorem constantRealization_underlying_eq (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D] (f : B →+* D) :
    (ModuleCat.restrictScalars f ⋙
      (ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
          koszulConstantFunctor X B)) ⋙ SheafOfModules.toSheaf (adicModuleRing X B) =
    ((ModuleCat.uliftFunctor.{t + 1, t} D ⋙ ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom ⋙
          koszulConstantFunctor X D) ⋙
      SheafOfModules.restrictScalars (adicModuleMap X f)) ⋙
        SheafOfModules.toSheaf (adicModuleRing X B) := by
  simp only [Functor.assoc, sheafRestrictionForget]
  have hB := constantRealization_forget X B
  have hD := constantRealization_forget X D
  simp only [Functor.assoc] at hB hD
  rw [hB, hD]
  simp only [← Functor.assoc, moduleRestrictionForget]

/-- Constant realization commutes naturally with restriction of coefficient scalars.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EL.
(blueprint: lem-weil-pbc-constant-realization-scalar-restriction).

Proof: use the canonical objectwise comparison induced by the module-sheafification
adjunction. Its underlying abelian sheaf map is the identity: the adjunction sends
it to the sheafification unit. Faithfulness of the forgetful functor therefore
proves naturality. This argument works for arbitrary rings and modules. -/
theorem constantRealization_restrictScalars (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D] (f : B →+* D) :
    Nonempty
      (ModuleCat.restrictScalars f ⋙
          (ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
            (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
              koszulConstantFunctor X B) ≅
        (ModuleCat.uliftFunctor.{t + 1, t} D ⋙ ModuleCat.restrictScalars.{t + 1}
            (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom ⋙
              koszulConstantFunctor X D) ⋙
          SheafOfModules.restrictScalars (adicModuleMap X f)) := by
  apply nonemptyIsoOfMappedComponents (SheafOfModules.toSheaf (adicModuleRing X B))
    (constantRealization_underlying_eq X f)
  intro M
  obtain ⟨e, he⟩ := constantRealization_restrictionIso_exists X f M
  refine ⟨e, ?_⟩
  rw [he]
  simp only [eqToHom_app]
  exact (eqToHom_refl _ _).symm

end AlgebraicGeometry.Scheme
