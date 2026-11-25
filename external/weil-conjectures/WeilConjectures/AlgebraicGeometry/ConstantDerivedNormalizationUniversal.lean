/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedNormalizationArrows
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

set_option linter.privateModule false

/-! # Constant realization preserves universal coefficient normalization

Source: Stacks Project, Tags 06YY, 07A4 and 0G7E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantNormalizationComparison

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R]

private def ringRestriction : realizationModules J R ⥤
    SheafOfModules.{max u v} ((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)) :=
  SheafOfModules.restrictScalars (realizationRingIso J R).inv

private theorem ringRestriction_equivalence : (ringRestriction J R).IsEquivalence := by
  let eC : C ≌ C := Equivalence.refl
  let : eC.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let : eC.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let c := (realizationRingIso J R).symm
  let e := SheafOfModules.pushforwardPushforwardEquivalence.{max u v}
    (J := J) (K := J) eC c.hom c.inv
    (by
      ext U x
      dsimp [eC, Equivalence.refl]
      simp only [CategoryTheory.Functor.map_id]
      exact congrArg (fun f ↦ f.hom.app U x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [eC, Equivalence.refl]
      simp only [CategoryTheory.Functor.map_id]
      exact congrArg (fun f ↦ f.hom.app U x) c.hom_inv_id)
  exact e.isEquivalence_functor

private instance constantDerivedNormalizationUniversalInst1
    : (ringRestriction J R).IsEquivalence := ringRestriction_equivalence J R

private instance constantDerivedNormalizationUniversalInst2
    : (constantRingModuleRestriction J R).IsEquivalence := by
  obtain ⟨⟨e, he, _⟩, _⟩ := constant_ring_module_sheaves J R
  rw [← he]
  infer_instance

private def restriction : realizationModules J R ⥤ Sheaf J (ModuleCat.{max u v} R) :=
  ringRestriction J R ⋙ constantRingModuleRestriction J R

private instance constantDerivedNormalizationUniversalInst3
    : (restriction J R).IsEquivalence := by unfold restriction; infer_instance
private instance constantDerivedNormalizationUniversalInst4 : (restriction J R).Additive where
  map_add := by intros; ext U x; rfl
private instance constantDerivedNormalizationUniversalInst5
    : PreservesFiniteLimits (restriction J R) := inferInstance
private instance constantDerivedNormalizationUniversalInst6
    : PreservesFiniteColimits (restriction J R) := inferInstance

private lemma ringIso_fac : realizationRingUnit J R ≫ (realizationRingIso J R).hom.hom =
    toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) := by
  dsimp only [realizationRingIso, Iso.app_hom]
  rw [constantCommuteCompose_hom_app_hom]
  unfold realizationRingUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of R)
      (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)

private lemma restriction_smul (M : realizationModules J R) (V : Cᵒᵖ) (r : R) (x : M.val.obj V) :
    r • (show ((restriction J R).obj M).obj.obj V from x) =
      (realizationRingUnit J R).app V r • x := by
  have h := congrArg (fun f ↦ f.app V r) (ringIso_fac J R)
  have hi := congrArg (fun f ↦ f.hom.app V) (realizationRingIso J R).hom_inv_id
  change (realizationRingIso J R).inv.hom.app V
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app V r) • x = _
  erw [← h]
  exact congrArg (fun a ↦ a • x) (ConcreteCategory.congr_hom hi _)

private instance constantDerivedNormalizationUniversalInst7
    : Presheaf.IsLocallyInjective J (realizationRingUnit J R) :=
  (realizationRingUnit_locallyBijective J R).1
private instance constantDerivedNormalizationUniversalInst8
    : Presheaf.IsLocallySurjective J (realizationRingUnit J R) :=
  (realizationRingUnit_locallyBijective J R).2

private def constantSeed (M : ModuleCat.{max u v} R) :
    (Functor.const Cᵒᵖ).obj M ⟶
      ((restriction J R).obj ((commutativeSiteConstantModuleFunctor J R).obj M)).obj where
  app V := by
    refine ConcreteCategory.ofHom (C := ModuleCat.{max u v} R) ?_
    refine { toFun := fun x ↦ ?_, map_add' := ?_, map_smul' := ?_ }
    · exact ((PresheafOfModules.sheafificationAdjunction
        (realizationRingUnit J R)).unit.app
          ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V x
    · intros; apply map_add
    · intro r x
      rw [restriction_smul]
      exact (((PresheafOfModules.sheafificationAdjunction
        (realizationRingUnit J R)).unit.app
          ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V).hom.map_smul r x
  naturality V W f := by
    ext x
    exact (PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
        ((siteConstantModulePresheafGeneral (C := C) R).obj M)) f x)

private def constantMap (M : ModuleCat.{max u v} R) :
    (constantSheaf J (ModuleCat.{max u v} R)).obj M ⟶
      (restriction J R).obj ((commutativeSiteConstantModuleFunctor J R).obj M) :=
  ((sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv _ _).symm
    (constantSeed J R M)

private lemma constantMap_fac (M : ModuleCat.{max u v} R) :
    toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ (constantMap J R M).hom =
      constantSeed J R M := by
  exact ((sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv _ _).apply_symm_apply _

private instance constantDerivedNormalizationUniversalInst9 (M : ModuleCat.{max u v} R) :
    Presheaf.IsLocallyInjective J (constantSeed J R M) where
  equalizerSieve_mem x y h :=
    Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        ((forget₂ (ModuleCat R) AddCommGrpCat).obj M))) x y h

private instance constantDerivedNormalizationUniversalInst10 (M : ModuleCat.{max u v} R) :
    Presheaf.IsLocallySurjective J (constantSeed J R M) where
  imageSieve_mem x :=
    Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        ((forget₂ (ModuleCat R) AddCommGrpCat).obj M))) x

private instance constantDerivedNormalizationUniversalInst11
    (M : ModuleCat.{max u v} R) : IsIso (constantMap J R M) := by
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · apply (Presheaf.comp_isLocallyInjective_iff J
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (constantMap J R M).hom).mp
    rw [constantMap_fac]
    infer_instance
  · apply (Presheaf.comp_isLocallySurjective_iff J
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (constantMap J R M).hom).mp
    rw [constantMap_fac]
    infer_instance

private theorem constantMap_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    (constantSheaf J (ModuleCat.{max u v} R)).map f ≫ constantMap J R N =
      constantMap J R M ≫ (restriction J R).map
        ((commutativeSiteConstantModuleFunctor J R).map f) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    (((restriction J R).obj ((commutativeSiteConstantModuleFunctor J R).obj N)).property)
  change toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
    ((constantSheaf J (ModuleCat.{max u v} R)).map f).hom ≫ (constantMap J R N).hom = _
  erw [← Category.assoc, ← toSheafify_naturality, Category.assoc, constantMap_fac]
  change _ = toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
    (constantMap J R M).hom ≫ _
  rw [← Category.assoc, constantMap_fac]
  ext V x
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      ((Functor.const Cᵒᵖ).map ((forget₂ (ModuleCat R) AddCommGrpCat).map f))) V) x

private def constantIso : constantSheaf J (ModuleCat.{max u v} R) ≅
    commutativeSiteConstantModuleFunctor J R ⋙ restriction J R :=
  NatIso.ofComponents (fun M ↦ asIso (constantMap J R M))
    (fun f ↦ constantMap_naturality J R f)

variable {S : Type (max u v)} [CommRing S] (q : R →+* S)

end CategoryTheory.ConstantNormalizationComparison

namespace CategoryTheory.ConstantNormalizationComparison
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (R : Type (u + 1)) [CommRing R]
  {S : Type (u + 1)} [CommRing S] (q : R →+* S)

private local instance (A : Type (u + 1)) [CommRing A] :
    HasDerivedCategory.{(u + 1) + 1} (realizationModules.{u + 1, u} J A) :=
  HasDerivedCategory.standard (realizationModules.{u + 1, u} J A)

end CategoryTheory.ConstantNormalizationComparison

namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]

end CategoryTheory
