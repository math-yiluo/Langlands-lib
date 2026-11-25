/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Constant rank-one modules and intrinsic coefficient realization

## References

* Stacks Project, Tags 00YV and 03CY, associated module sheaves and restriction of scalars
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- The constant coefficient ring as its own module, with its actual sectionwise action. -/
noncomputable abbrev proEtaleConstantModule (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  SheafOfModules.unit ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))

/-- The fixed-scalar constant rank-one module before the intrinsic realization. -/
noncomputable abbrev proEtaleFixedConstantModule (X : Scheme.{u})
    (A : Type u) [CommRing A] :=
  (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))

private noncomputable def unitRestriction (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) := by
  let P := (PresheafOfModules.restrictScalars
    (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).obj (proEtaleConstantModule X A).val
  let F : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} A) :=
    { obj := P.obj
      map := P.map
      map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
      map_comp f g := by
        ext x
        exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
  exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology X) F
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})
    (proEtaleConstantModule X A).isSheaf⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def unitScalar (X : Scheme.{u}) (A : Type u) [CommRing A] :
    (Functor.const X.ProEtᵒᵖ).obj
        (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ⟶
      (unitRestriction X A).obj where
  app W := by
    letI := ((unitRestriction X A).obj.obj W).isModule
    exact ModuleCat.ofHom
      (X := ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
      (Y := (unitRestriction X A).obj.obj W)
      { toFun := (ProEtale.finiteCoefficientIntrinsicScalarMap X A).app W
        map_add' := map_add _
        map_smul' := fun r a ↦ by
          change (ProEtale.finiteCoefficientIntrinsicScalarMap X A).app W (r * a) =
            (ProEtale.finiteCoefficientIntrinsicScalarMap X A).app W r *
              (ProEtale.finiteCoefficientIntrinsicScalarMap X A).app W a
          exact map_mul _ r a }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact ConcreteCategory.congr_hom
      ((ProEtale.finiteCoefficientIntrinsicScalarMap X A).naturality f) a

private noncomputable def unitFixedMap (X : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleFixedConstantModule X A ⟶ unitRestriction X A :=
  ⟨sheafifyLift (ProEt.topology X) (unitScalar X A) (unitRestriction X A).property⟩

private lemma unitFixedMap_fac (X : Scheme.{u}) (A : Type u) [CommRing A] :
    toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))) ≫
      (unitFixedMap X A).hom = unitScalar X A :=
  toSheafify_sheafifyLift _ _ _

set_option backward.isDefEq.respectTransparency false in
private instance unitScalar_locallyInjective (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    Presheaf.IsLocallyInjective (ProEt.topology X) (unitScalar X A) where
  equalizerSieve_mem x y h := Presheaf.equalizerSieve_mem (ProEt.topology X)
    (ProEtale.finiteCoefficientIntrinsicScalarMap X A) x y h

set_option backward.isDefEq.respectTransparency false in
private instance unitScalar_locallySurjective (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    Presheaf.IsLocallySurjective (ProEt.topology X) (unitScalar X A) where
  imageSieve_mem x := Presheaf.imageSieve_mem (ProEt.topology X)
    (ProEtale.finiteCoefficientIntrinsicScalarMap X A) x

private instance unitFixedMap_isIso (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] : IsIso (unitFixedMap X A) := by
  let η := toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))
  have hfac : η ≫ (unitFixedMap X A).hom = unitScalar X A := unitFixedMap_fac X A
  have hi : Presheaf.IsLocallyInjective (ProEt.topology X) (unitFixedMap X A).hom := by
    rw [← Presheaf.comp_isLocallyInjective_iff (ProEt.topology X) η, hfac]
    infer_instance
  have hs : Presheaf.IsLocallySurjective (ProEt.topology X) (unitFixedMap X A).hom := by
    rw [← Presheaf.comp_isLocallySurjective_iff (ProEt.topology X) η, hfac]
    infer_instance
  exact (Sheaf.isLocallyBijective_iff_isIso (unitFixedMap X A)).mp ⟨hi, hs⟩

/-- The rank-one realization isomorphism is uniquely fixed on all constant generators. -/
theorem proEtaleConstantModuleUnit_existsUnique (X : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    ∃! e : (sfIntrinsicModuleEquivalence X A).functor.obj
        (proEtaleFixedConstantModule X A) ≅ proEtaleConstantModule X A,
      ∀ (W : X.ProEtᵒᵖ) (a : ULift.{u + 1, u} A),
        e.hom.val.app W
          (sfIntrinsicRealizationUnit X A (proEtaleFixedConstantModule X A) W
            ((toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj
                (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app W a)) =
          (ProEtale.finiteCoefficientIntrinsicScalarMap X A).app W a := by
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap X A
  let E := ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)
  let P := E.obj (proEtaleFixedConstantModule X A).obj
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1} α
  let G := SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars α
  let g : P ⟶ G.obj (proEtaleConstantModule X A) :=
    E.map (unitFixedMap X A).hom
  have : IsIso g := by
    change IsIso (E.map ((sheafToPresheaf _ _).map (unitFixedMap X A)))
    infer_instance
  let f0 : (PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} α).obj P ⟶
      proEtaleConstantModule X A :=
    (adj.homEquiv P (proEtaleConstantModule X A)).symm g
  let f : (sfIntrinsicModuleEquivalence X A).functor.obj
      (proEtaleFixedConstantModule X A) ⟶ proEtaleConstantModule X A := f0
  have : IsIso f0 := by
    dsimp only [f0]
    rw [adj.homEquiv_counit]
    infer_instance
  have hfg : adj.unit.app P ≫ G.map f0 = g := by
    change adj.homEquiv P (proEtaleConstantModule X A) f0 = g
    exact (adj.homEquiv P (proEtaleConstantModule X A)).apply_symm_apply g
  have hf (W : X.ProEtᵒᵖ) (a : ULift.{u + 1, u} A) :
      f.val.app W
        (sfIntrinsicRealizationUnit X A (proEtaleFixedConstantModule X A) W
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app W a)) =
        α.app W a := by
    have h := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app W) hfg)
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app W a)
    have h' := ConcreteCategory.congr_hom (congr_app (unitFixedMap_fac X A) W) a
    exact h.trans h'
  refine ⟨asIso f, hf, ?_⟩
  intro e he
  apply Iso.ext
  apply (adj.homEquiv P (proEtaleConstantModule X A)).injective
  change adj.homEquiv P _ e.hom = adj.homEquiv P _ f
  rw [show adj.homEquiv P _ f = g from
    (adj.homEquiv P _).apply_symm_apply g]
  let q := adj.homEquiv P (proEtaleConstantModule X A) e.hom
  let q' : (proEtaleFixedConstantModule X A).obj ⟶ (unitRestriction X A).obj :=
    { app := q.app
      naturality {U V} k := by
        ext x
        exact ConcreteCategory.congr_hom (q.naturality k) x }
  have hq : q' = (unitFixedMap X A).hom := by
    apply sheafify_hom_ext (ProEt.topology X) _ _ (unitRestriction X A).property
    rw [unitFixedMap_fac]
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact he W a
  change q = E.map (unitFixedMap X A).hom
  ext W x
  exact ConcreteCategory.congr_hom (congr_app hq W) x

/-- The unique comparison preserving constant scalar sections; no module data are chosen
from a mere existence assertion. -/
noncomputable def proEtaleConstantModuleUnit (X : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicModuleEquivalence X A).functor.obj
      (proEtaleFixedConstantModule X A) ≅ proEtaleConstantModule X A :=
  (proEtaleConstantModuleUnit_existsUnique X A).exists.choose

end AlgebraicGeometry.Scheme
