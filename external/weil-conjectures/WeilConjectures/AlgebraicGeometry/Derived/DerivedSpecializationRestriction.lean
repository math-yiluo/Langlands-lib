/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalDerivedRestriction
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFibreRestriction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality

/-! # Derived specialization factors through strict-local sections

Source: Stacks Project, Tag 0GJ2, Remark alternative-sp.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

section ExactComparisons

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private lemma exactComparison_inv (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory.Plus C) :
    F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
        (_root_.DerivedCategory.Plus.Qh.obj K) =
      F.mapDerivedCategoryPlusFactorsh.hom.app K ≫ F.rightDerivedFunctorPlusUnith.app K := by
  apply (cancel_mono (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
    (_root_.DerivedCategory.Plus.Qh.obj K))).mp
  have h := congr_app F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app] using
      (congrArg (fun a ↦ F.mapDerivedCategoryPlusFactorsh.hom.app K ≫ a) h).symm

private lemma exactDerived_fac (τ : F ⟶ G) (K : HomotopyCategory.Plus C) :
    F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
        (_root_.DerivedCategory.Plus.Qh.obj K) ≫
      (Functor.rightDerivedFunctorPlusNatTrans τ).app
        (_root_.DerivedCategory.Plus.Qh.obj K) ≫
      G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
        (_root_.DerivedCategory.Plus.Qh.obj K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app K =
    F.mapDerivedCategoryPlusFactorsh.hom.app K ≫
      _root_.DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus τ).app K) := by
  rw [exactComparison_inv F K, Category.assoc,
    Functor.rightDerivedFunctorPlusNatTrans_app_assoc]
  have h := congr_app G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [← Category.assoc (G.rightDerivedFunctorPlusUnith.app K), h]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Category.comp_id]

end ExactComparisons

private lemma exactDerived_factorization
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    (A Z : C ⥤ E) (L : C ⥤ D) (B T : D ⥤ E)
    [A.Additive] [Z.Additive] [L.Additive] [B.Additive] [T.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (r : A ⟶ L ⋙ B) (b : B ⟶ T) (e : L ⋙ T ≅ Z) :
    A.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv ≫
        Functor.rightDerivedFunctorPlusNatTrans (r ≫ Functor.whiskerLeft L b ≫ e.hom) ≫
        Z.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom =
      A.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv ≫
        Functor.rightDerivedFunctorPlusNatTrans r ≫
        (L ⋙ B).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom ≫
        (Functor.mapDerivedCategoryPlusCompIso L B).hom ≫
        Functor.whiskerLeft L.mapDerivedCategoryPlus
          (B.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv ≫
            Functor.rightDerivedFunctorPlusNatTrans b ≫
            T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom) ≫
        (Functor.mapDerivedCategoryPlusCompIso L T).inv ≫
        (Functor.mapDerivedCategoryPlusNatIso e).hom := by
  let db := B.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv ≫
    Functor.rightDerivedFunctorPlusNatTrans b ≫
    T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
  refine Localization.natTrans_ext _root_.DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (fun K ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_mono (Z.mapDerivedCategoryPlusFactorsh.hom.app K)).mp
  simp only [Category.assoc]
  rw [exactDerived_fac, Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  have hi : (Functor.mapDerivedCategoryPlusCompIso L T).inv.app
        (_root_.DerivedCategory.Plus.Qh.obj K) ≫
      (L ⋙ T).mapDerivedCategoryPlusFactorsh.hom.app K =
    T.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      T.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) := by
    apply (cancel_epi ((Functor.mapDerivedCategoryPlusCompIso L T).hom.app
      (_root_.DerivedCategory.Plus.Qh.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact (Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh L T K).symm
  rw [← Category.assoc ((Functor.mapDerivedCategoryPlusCompIso L T).inv.app _), hi]
  have hn := db.naturality (L.mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [db, NatTrans.comp_app, Functor.comp_obj, Category.assoc] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  have hb := exactDerived_fac b (L.mapHomotopyCategoryPlus.obj K)
  rw [reassoc_of% hb]
  rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh_assoc]
  have hr := exactDerived_fac r K
  rw [reassoc_of% hr]
  have hw := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerLeft_app L b K
  simp only [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app, Functor.comp_obj,
    Category.id_comp, Category.comp_id] at hw
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
    Functor.map_comp, hw]

/-- Specialization is restriction to strict-local sections followed by the global germ
and the inverse-image stalk identification.
Source: Stacks Project, Tag 0GJ2, Remark alternative-sp, and Tag 03Q1 (3).
(blueprint: lem-weil-pbc-derived-specialization-restriction).

Proof: underived specialization is by definition the uniquely characterized restriction
of germs, followed by the terminal-section germ and the inverse-image stalk comparison.
The terminal-section germ is globalGerm. Derive this equality of natural transformations.
The source stalk, inverse image, strict-local global sections and target stalk are exact,
so their right derived functors are canonically the functors computed termwise. The
composition isomorphism for termwise exact functors separates inverse image and global
sections. Naturality of this composition isomorphism carries the terminal germ to the
derived global germ; the exact-functor comparison carries the inverse-image stalk
isomorphism to derivedPullbackStalkIso. The two adjacent exact-global-sections
comparisons cancel. Equivalently, check on Qh of a bounded-below complex using the
right-derived unit formulas: both sides become the localization of the same degreewise
specialization map. Right-derived extensionality proves the stated equality. -/
theorem derivedEtaleStalkSpecialization_restriction
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    (K : _root_.DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedEtaleStalkSpecialization s t).app K =
      (strictLocalDerivedRestriction s).app K ≫
        (derivedGlobalGermAt t).app
          ((upperStar AddCommGrpCat.{u + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj K) ≫
        (derivedPullbackStalkIso (Scheme.strictHenselizationStructuralMap s) t).hom.app K := by
  let L := upperStar AddCommGrpCat.{u + 1} (Scheme.strictHenselizationStructuralMap s)
  let A := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let Z := (Scheme.pointSmallEtale
    (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber (A := AddCommGrpCat.{u + 1})
  let B := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{u + 1}
  let T := (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
  let e := upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
    (Scheme.strictHenselizationStructuralMap s) t
  have hτ : etaleStalkSpecializationNatTrans s t =
      strictLocalRestrictionNat s ≫ Functor.whiskerLeft L (globalGerm t) ≫ e.hom := by
    ext F
    rfl
  have h := congr_app (exactDerived_factorization A Z L B T
    (strictLocalRestrictionNat s) (globalGerm t) e) K
  rw [← hτ] at h
  simpa only [derivedEtaleStalkSpecialization, strictLocalDerivedRestriction,
    derivedGlobalGermAt, derivedPullbackStalkIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc,
    Iso.inv_hom_id_app_assoc] using h

end AlgebraicGeometry.Etale
