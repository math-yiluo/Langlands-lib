/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteEquivalenceHomTransport
import WeilConjectures.CategoryTheory.Ringed.RingedOpenDerivedHomAdjunction
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison

/-! # Internal Hom from integral open extension by zero

## References

* Bhatt--Scholze, Lemma 6.3.14(3)
* Stacks Tags 0E8I and 06YN
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Internal Hom out of open extension by zero is open direct image of internal
Hom into the open restriction. All coefficients are the identified completed rings. -/
theorem integralOpen_homPushforward
    {U T : Scheme.{u}} {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (j : U ⟶ T) [IsOpenImmersion j]
    (P : DerivedCategory (pbcModules U (pbcAdicCompletion U d))) :
    Nonempty (RingedHomUniverses.hom.{u + 1, u, u + 1}
      (ProEt.topology T) (pbcAdicCompletion T d) ((cbcJ d j).obj P) ≅
      d.pull j ⋙ RingedHomUniverses.hom.{u + 1, u, u + 1}
        (ProEt.topology U) (pbcAdicCompletion U d) P ⋙ d.push j) := by
  classical
  let W := cbcOpenObject j inferInstance
  let e := ProEt.sliceEquiv T W
  let : e.inverse.IsDenseSubsite (ProEt.topology U) ((ProEt.topology T).over W) :=
    ProEt.sliceDense T W
  let : e.functor.IsContinuous ((ProEt.topology T).over W) (ProEt.topology U) :=
    cbcSliceFunctor_continuous T W
  let : e.functor.IsDenseSubsite ((ProEt.topology T).over W) (ProEt.topology U) := by
    have h := e.eq_inducedTopology_of_isDenseSubsite
      ((ProEt.topology T).over W) (ProEt.topology U)
    rw [h]
    infer_instance
  let : e.symm.inverse.IsDenseSubsite ((ProEt.topology T).over W) (ProEt.topology U) :=
    inferInstanceAs
      (e.functor.IsDenseSubsite ((ProEt.topology T).over W) (ProEt.topology U))
  let R := pbcAdicCompletion T d
  let S := pbcAdicCompletion U d
  let c := completedSliceIso W d
  obtain ⟨E, ha, ⟨ε⟩, ⟨γ⟩⟩ :=
    CategoryTheory.NativeRestriction.siteCoefficientEquivalence_derivedHom.{
      u + 1, u + 1, u, u, u + 1, u + 2, u + 2} e.symm S (R.over W) c
  let := ha
  have hc : cbcCompletedSliceMap d T W = c.hom :=
    (cbcCompletedSliceMap_exists d T W).unique
      (cbcCompletedSliceMap_exists d T W).exists.choose_spec
      (completedSliceIso_projection W d)
  let ε' : E.functor ≅ cbcModuleToSlice d T W := by
    simpa only [cbcModuleToSlice, hc] using ε
  let Q := E.mapDerivedCategory
  let EX : RingedDerivedNative.Modules.{u + 1, u, u + 1}
      ((ProEt.topology T).over W) (R.over W) ⥤
        RingedDerivedNative.Modules.{u + 1, u, u + 1} (ProEt.topology T) R :=
    SheafOfModules.localizedSystemExtension.{u + 1, u, u + 1} R W
  let RE : RingedDerivedNative.Modules.{u + 1, u, u + 1} (ProEt.topology T) R ⥤
      RingedDerivedNative.Modules.{u + 1, u, u + 1}
        ((ProEt.topology T).over W) (R.over W) :=
    SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1} R W
  let : EX.Additive :=
    SheafOfModules.localizedSystemExtensionAdditive.{u + 1, u, u + 1} R W
  let : RE.Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{u + 1, u, u + 1} R W
  let : PreservesFiniteLimits EX :=
    SheafOfModules.localizedSystemExtensionLimits.{u + 1, u, u + 1} R W
  let : PreservesFiniteColimits EX :=
    SheafOfModules.localizedSystemExtensionColimits.{u + 1, u, u + 1} R W
  let : PreservesFiniteLimits RE :=
    SheafOfModules.localizedSystemRestrictionLimits.{u + 1, u, u + 1} R W
  let : PreservesFiniteColimits RE :=
    SheafOfModules.localizedSystemRestrictionColimits.{u + 1, u, u + 1} R W
  let a : EX.mapDerivedCategory ⊣ RE.mapDerivedCategory :=
    (SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1} R W).mapExactDerivedCategory
  let eJ : cbcJ d j ≅ Q.functor ⋙ EX.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight ε'.symm EX) ≪≫
      (Functor.mapDerivedCategoryCompIso E.functor EX).symm
  let ep : d.pull j ≅ RE.mapDerivedCategory ⋙ Q.inverse :=
    ((cbcDerivedOpenAdjunction d j).ofNatIsoLeft eJ).rightAdjointUniq
      (Q.toAdjunction.comp a)
  let er : RE.mapDerivedCategory ≅ d.pull j ⋙ Q.functor :=
    (Functor.rightUnitor RE.mapDerivedCategory).symm ≪≫
      Functor.isoWhiskerLeft RE.mapDerivedCategory Q.counitIso.symm ≪≫
      Functor.isoWhiskerRight ep.symm Q.functor
  let G := Q.inverse ⋙ d.push j
  let ag : RE.mapDerivedCategory ⊣ G :=
    ((cbcPullPushAdjunction d j).comp Q.toAdjunction).ofNatIsoLeft er.symm
  obtain ⟨eh⟩ := ringedOpenDerived_homAdjunction.{
    u + 1, u, u + 1, u + 2} (ProEt.topology T) R W
      G ag (Q.functor.obj P)
  let hU := RingedHomUniverses.hom.{u + 1, u, u + 1} (ProEt.topology U) S P
  let hW := RingedHomUniverses.hom.{u + 1, u, u + 1}
    ((ProEt.topology T).over W) (R.over W) (Q.functor.obj P)
  let hq : hU ⋙ Q.functor ≅ Q.functor ⋙ hW :=
    (Functor.curry.mapIso γ).app (op P) ≪≫
      (Functor.curryObjProdComp Q.functor.op Q.functor
        (derivedInternalHomOfUniverses.{u + 1, u, u + 1}
          ((ProEt.topology T).over W) (R.over W))).app (op P)
  exact ⟨((Functor.curry.obj (derivedInternalHomOfUniverses.{
      u + 1, u, u + 1} (ProEt.topology T) R)).mapIso (eJ.app P).op).symm ≪≫
    eh ≪≫ Functor.isoWhiskerRight er (hW ⋙ Q.inverse ⋙ d.push j) ≪≫
    Functor.isoWhiskerLeft (d.pull j)
      (Functor.isoWhiskerRight hq.symm (Q.inverse ⋙ d.push j)) ≪≫
    Functor.isoWhiskerLeft (d.pull j ⋙ hU)
      (Functor.isoWhiskerRight Q.unitIso.symm (d.push j))⟩

end AlgebraicGeometry.Scheme
