/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
import WeilConjectures.CategoryTheory.Sites.SheafComposeForgetModule
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
import all WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors

/-! # The normalized tensor structure of the canonical finite coefficient equivalence

Source: the coefficient-presentation step in det-thm-sf-pf-finite.proof.md.
(blueprint: lem-d5-canonical-finite-coefficient-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Mod.monoidalClosed
open FiniteDiscreteOrdinary

/-- Normalization on the original local sections (blueprint:
lem-d5-canonical-finite-coefficient-tensor). -/
def CanonicalFiniteTensorNormalized
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] (X : Scheme.{u})
    (m : (finiteCoefficientModEquivalence X A).functor.Monoidal) : Prop :=
  ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj A) X))
        (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        ((m.toLaxMonoidal.μ M N).hom.app V)
          (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology X)
            (ULift.{u + 1} A)
            ((finiteCoefficientModEquivalence X A).functor.obj M)
            ((finiteCoefficientModEquivalence X A).functor.obj N) V x y) =
          InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj A) X) M N V x y


section

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A] (X : Scheme.{u})

private def scalarConstants :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X).obj :=
  toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (constRingSheafToCondensedRingObj X A).hom

private local instance scalarTargetMonObj :
    MonObj (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X).obj :=
  (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).monObjObj
    (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X)

private instance scalarConstants_monoid : IsMonHom (scalarConstants A X) := by
  let J := Scheme.ProEt.topology X
  let P := (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))
  let mP := (Functor.const X.ProEtᵒᵖ).monObjObj (AddCommGrpCat.of (ULift.{u + 1} A))
  let c := constRingSheafToCondensedRingObj X A
  have hc0 : IsMonHom c := inferInstance
  let mS := (presheafToSheaf J Ab.{u + 1}).monObjObj P
  have hp : mP = Functor.monObjCompForget₂
      ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) := by
    apply MonObj.ext
    ext V
    rfl
  have hm : Sheaf.monObj_presheafToSheaf_obj J
      (Presheaf.constRingObj (C := X.ProEt) (ULift.{u + 1} A)) = mS := by
    exact congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
      (presheafToSheaf J Ab.{u + 1}) _ _ m) hp.symm
  have hc := IsMonHom.of_eq c hm rfl (hf := hc0)
  have hu := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
  have hf := monHomMapExplicit (sheafToPresheaf J Ab.{u + 1}) mS _ c
    hc
  exact monHomCompExplicit mP _ _ _ _ hu hf

private def scalarRingConstants :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X)).obj :=
  constantSectionRingMapAux (Scheme.ProEt.topology X) (ULift.{u + 1} A)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X) (scalarConstants A X)

private abbrev canonicalSectionRing (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (X : Scheme.{u}) : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X)

private def scalarRingMap :
    realizationRing (Scheme.ProEt.topology X) (ULift.{u + 1} A) ⟶
      canonicalSectionRing A X :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    _ (canonicalSectionRing A X)).symm (scalarRingConstants A X)

omit [DiscreteTopology A] [Finite A] in
private theorem scalarRingMap_normalized (V : X.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
    (scalarRingMap A X).hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app V a) =
      (scalarConstants A X).app V a := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology X)
    CommRingCat.{u + 1}).homEquiv _
      (canonicalSectionRing A X)).apply_symm_apply (scalarRingConstants A X)
  exact ConcreteCategory.congr_hom (congr_app h V) a

private theorem scalarRingMap_isIso : IsIso (scalarRingMap A X) := by
  let J := Scheme.ProEt.topology X
  let B := ULift.{u + 1} A
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : J.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification J V
  let F := sheafCompose J V
  let e := (constantCommuteCompose J V).app (CommRingCat.of B)
  let g : F.obj (realizationRing J B) ⟶
      condensedRingObj (Profinite.continuousMapRingObj.{u} A) X :=
    F.map (scalarRingMap A X)
  have hg : e.inv ≫ g = constRingSheafToCondensedRingObj X A := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _
      (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X).property
    have he : toSheafify J
        ((Functor.const X.ProEtᵒᵖ).obj (V.obj (CommRingCat.of B))) ≫ e.inv.hom =
        Functor.whiskerRight
          (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) V := by
      change _ ≫ (sheafifyMap J (Functor.constComp X.ProEtᵒᵖ
        (CommRingCat.of B) V).inv ≫ (sheafifyComposeIso J V _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        sheafComposeIso_hom_fac]
      ext U a
      rfl
    change _ ≫ (e.inv.hom ≫ g.hom) = _
    rw [← Category.assoc, he]
    ext U a
    exact scalarRingMap_normalized A X U a
  have : IsIso (e.inv ≫ g) := hg.symm ▸ inferInstance
  have : IsIso g := by
    have hh : g = e.hom ≫ (e.inv ≫ g) := by simp
    rw [hh]
    infer_instance
  exact isIso_of_reflects_iso (scalarRingMap A X) F

private def heartEncoding :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X) ⥤
        Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} A) X)).functor ⋙
  SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarRingMap A X)) ⋙
  ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) (ULift.{u + 1} A)

private theorem heartEncoding_normalized :
    ∃ m : (heartEncoding A X).Monoidal,
      ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj A) X))
        (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        ((m.toLaxMonoidal.μ M N).hom.app V)
          (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology X)
            (ULift.{u + 1} A) ((heartEncoding A X).obj M)
              ((heartEncoding A X).obj N) V x y) =
          InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj A) X) M N V x y := by
  obtain ⟨ms, hs⟩ := section_monoidal_normalized
    (Scheme.ProEt.topology X) (condensedRingObj (Profinite.continuousMapRingObj A) X)
  let := ms
  have := scalarRingMap_isIso A X
  let := HasDerivedCategory.standard
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (canonicalSectionRing A X)))
  let := HasDerivedCategory.standard
    (SheafOfModules.scalarModules (Scheme.ProEt.topology X)
      (realizationRing (Scheme.ProEt.topology X) (ULift.{u + 1} A)))
  obtain ⟨r⟩ := SheafOfModules.ringIso_tensor_transport (asIso (scalarRingMap A X))
  let : (SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarRingMap A X))).Monoidal :=
    r.monoidal.toMonoidal
  let : (ConstantScalarRestriction.restriction (Scheme.ProEt.topology X)
      (ULift.{u + 1} A)).Monoidal :=
    (ConstantScalarRestriction.ordinary (Scheme.ProEt.topology X)
      (ULift.{u + 1} A)).braided.toMonoidal
  let : (heartEncoding A X).Monoidal := by
    unfold heartEncoding
    infer_instance
  refine ⟨inferInstance, ?_⟩
  intro M N V x y
  let S := (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology X) (condensedRingObj (Profinite.continuousMapRingObj A) X)).functor
  let H := SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarRingMap A X))
  have hr := r.pure_inv (S.obj M) (S.obj N) V x y
  have hc := (ConstantScalarRestriction.ordinary (Scheme.ProEt.topology X)
    (ULift.{u + 1} A)).tensor_inv (H.obj (S.obj M)) (H.obj (S.obj N)) V x y
  let fS := (Functor.LaxMonoidal.μ S M N).val.app V
  let fR := (r.monoidal.toMonoidal.toLaxMonoidal.μ (S.obj M) (S.obj N)).val.app V
  exact (congrArg (fun z ↦ fS (fR z)) hc).trans
    ((congrArg (fun z ↦ fS z) hr).trans (hs M N V x y))

omit [DiscreteTopology A] [Finite A] in
private theorem heart_smul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))
    (V : X.ProEtᵒᵖ) (a : ULift.{u + 1} A) (m : M.X.obj.obj V) :
    (show M.X.obj.obj V from a •
      (show ((heartEncoding A X).obj M).obj.obj V from m)) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj A) X) M.X).app V ≫
        (Mod.act M.X).hom.app V).hom ((scalarConstants A X).app V a ⊗ₜ[ℤ] m) := by
  let J := Scheme.ProEt.topology X
  let B := ULift.{u + 1} A
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of B)
  have hc : realizationRingUnit J B ≫ c.hom.hom =
      toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B)) := by
    change _ ≫ ((constantCommuteCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of B)).hom = _
    erw [constantCommuteCompose_hom_app_hom]
    unfold realizationRingUnit
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of B)
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  have hi : toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B)) ≫ c.inv.hom =
      realizationRingUnit J B := by
    rw [← hc, Category.assoc]
    change _ ≫ (c.hom ≫ c.inv).hom = _
    rw [Iso.hom_inv_id]
    exact Category.comp_id _
  change ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X) M.X).app V ≫
      (Mod.act M.X).hom.app V).hom
    ((scalarRingMap A X).hom.app V (c.inv.hom.app V
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B))).app V a)) ⊗ₜ[ℤ] m) = _
  erw [ConcreteCategory.congr_hom (congr_app hi V) a]
  apply congrArg (fun r ↦ ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj A) X) M.X).app V ≫
      (Mod.act M.X).hom.app V).hom (r ⊗ₜ[ℤ] m))
  exact scalarRingMap_normalized A X V a

private theorem canonical_smul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))
    (V : X.ProEtᵒᵖ) (a : ULift.{u + 1} A) (m : M.X.obj.obj V) :
    (show M.X.obj.obj V from a •
      (show ((finiteCoefficientModEquivalence X A).functor.obj M).obj.obj V from m)) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj A) X) M.X).app V ≫
        (Mod.act M.X).hom.app V).hom ((scalarConstants A X).app V a ⊗ₜ[ℤ] m) := by
  let J := Scheme.ProEt.topology X
  let U := sheafToPresheaf J Ab.{u + 1}
  let c := constRingSheafToCondensedRingObj X A
  have h := Functor.LaxMonoidal.μ_natural_left_assoc U c M.X (U.map (Mod.act M.X))
  change Presheaf.modSmul
    ((Sheaf.modToPresheafMod J (ULift.{u + 1} A)).obj ((Mod.comap c).obj M)) V a m = _
  dsimp only [Presheaf.modSmul, Presheaf.actHom, Presheaf.actApp]
  change ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} A)))).app V ▷ _ ≫
    (Functor.LaxMonoidal.μ U _ M.X).app V ≫
    (U.map (c ▷ M.X ≫ Mod.act M.X)).app V).hom (a ⊗ₜ[ℤ] m) = _
  simp only [Functor.map_comp, NatTrans.comp_app,
    AddCommGrpCat.comp_apply, AddCommGrpCat.MonoidalCategory.whiskerRight_tmul]
  have hh := congrArg (fun k ↦ (AddCommGrpCat.Hom.hom (k.app V))
    ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app V a ⊗ₜ[ℤ] m)) h
  change _ = (AddCommGrpCat.Hom.hom ((U.map (Mod.act M.X)).app V))
    (((Functor.LaxMonoidal.μ U _ _).app V).hom
      (((U.map c).app V).hom
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} A)))).app V a) ⊗ₜ[ℤ] m))
  have hw : (((U.map c).app V ▷ (U.obj M.X).obj V).hom
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app V a ⊗ₜ[ℤ] m)) =
      ((U.map c).app V).hom
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} A)))).app V a) ⊗ₜ[ℤ] m := by
    rfl
  simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply, Monoidal.whiskerRight_app] at hh
  erw [hw] at hh
  exact hh.symm


-- Identifying the two scalar restrictions reduces their explicit section actions.
private def heartCanonicalIso :
    heartEncoding A X ≅ (finiteCoefficientModEquivalence X A).functor :=
  Sheaf.natIsoMkOfSheafCompose
    (F₁ := heartEncoding A X) (F₂ := (finiteCoefficientModEquivalence X A).functor)
    (fun M ↦ Iso.refl _)
    (fun M V a m ↦ (heart_smul A X M V a m).trans (canonical_smul A X M V a m).symm)
    (fun g ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)

end

private theorem uniqueNormalizedTensor
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] (X : Scheme.{u})
    (m n : (finiteCoefficientModEquivalence X A).functor.Monoidal)
    (hm : CanonicalFiniteTensorNormalized A X m)
    (hn : CanonicalFiniteTensorNormalized A X n) : m = n := by
  apply Functor.Monoidal.toLaxMonoidal_injective
  apply ModuleRingedComparison.laxMonoidal_ext_mu
  intro M N
  apply ConstantScalarRestriction.fixedTensor_ext
    (Scheme.ProEt.topology X) (ULift.{u + 1} A)
  intro V x y
  exact (hm M N V x y).trans (hn M N V x y).symm



section
variable (A : Type) [CommRing A]
private theorem canonicalFixed_tensor_pure (T : Scheme.{u})
    {M M' N N' : Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (f : M ⟶ M') (g : N ⟶ N') (V : T.ProEtᵒᵖ)
    (x : M.obj.obj V) (y : N.obj.obj V) :
    ((f ⊗ₘ g).hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
          M N V x y) =
      ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
        M' N' V ((f.hom.app V) x) ((g.hom.app V) y) := by
  exact (congrArg (fun z ↦ (z.app V) (x ⊗ₜ[ULift.{u + 1} A] y))
    (Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) f g)).symm

end

/-- The canonical finite coefficient equivalence has its unique section-normalized
strong monoidal structure.

Source: det-thm-sf-pf-finite.proof.md, coefficient realization; the balanced tensor
construction of Modules on Sites, Stacks Tags 03CY and 03EK.
(blueprint: lem-d5-canonical-finite-coefficient-tensor).

Proof: restrict scalars along constRingSheafToCondensedRingObj and apply the
constant-ring module/sheaf equivalence. A balanced pairing of the resulting fixed
scalar sheaves is the same as a pairing balanced over the internal coefficient ring:
constant scalar sections generate the constant ring sheaf locally. Sheafifying the
two universal balanced pairings gives inverse tensor maps. Their tensorator sends a
pair of local sections to the same internal pure tensor, giving the formula below.
The regular module gives the unit comparison. Naturality, associativity and both
unit identities can be checked on local pure tensors. These comparisons are
isomorphisms by the two universal properties. Pure tensors generate the sheafified
tensor, so the formula uniquely determines every tensorator. The unit map is then
determined by the unit identities (equivalently, uniqueness of a unit for a fixed
multiplication). Thus the monoidal structure is unique. No nonempty-scheme or
nonzero-ring assumption is used. -/
theorem canonicalFiniteCoefficientTensor
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] (X : Scheme.{u}) :
    ∃! m : (finiteCoefficientModEquivalence X A).functor.Monoidal,
      CanonicalFiniteTensorNormalized A X m := by
  obtain ⟨m, hm⟩ := heartEncoding_normalized A X
  let := m
  let i := heartCanonicalIso A X
  let m' := Functor.Monoidal.transport i
  have hm' : CanonicalFiniteTensorNormalized A X m' := by
    intro M N V x y
    change ((((i.inv.app M ⊗ₘ i.inv.app N) ≫
      m.toLaxMonoidal.μ M N ≫ i.hom.app (M ⊗ N)).hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology X)
          (ULift.{u + 1} A) _ _ V x y)) = _
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ModuleCat.comp_apply]
    rw [canonicalFixed_tensor_pure A]
    change ((m.toLaxMonoidal.μ M N).hom.app V)
      (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology X)
        (ULift.{u + 1} A) _ _ V x y) = _
    exact hm M N V x y
  refine ⟨m', hm', ?_⟩
  intro n hn
  exact uniqueNormalizedTensor A X n m' hn hm'


end AlgebraicGeometry.ProEtale
