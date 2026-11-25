/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCech
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
import WeilConjectures.AlgebraicGeometry.FlatRingedCechBaseChangeQuasiIso

/-! # Flat base change of the global augmented Cech model

Source: Stacks Project, Algebraization, Tag 099I, second paragraph, using Tag 099H.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local irreducible] SheafOfModules.RingedTensor.tensorAdjunction
  SheafOfModules.RingedTensor.tensorFunctor
  Adjunction.mapHomologicalComplex

private theorem augmented_model_of_adjunction
    {A D : Type*} [Category A] [Abelian A] [Category D] [Abelian D]
    {F : CochainComplex A ℤ ⥤ CochainComplex D ℤ}
    {G : CochainComplex D ℤ ⥤ CochainComplex A ℤ}
    (adj : F ⊣ G) (K : CochainComplex A ℤ) (T : CochainComplex D ℤ)
    (f : K ⟶ G.obj T) (h : QuasiIso (adj.unit.app K)) :
    ∃ (L : CochainComplex D ℤ) (δ : L ⟶ T) (u : K ⟶ G.obj L),
      QuasiIso u ∧ u ≫ G.map δ = f := by
  refine ⟨F.obj K, (adj.homEquiv K T).symm f, adj.unit.app K, h, ?_⟩
  exact (adj.homEquiv_apply _ _ _).symm.trans ((adj.homEquiv K T).apply_symm_apply f)

/-- Termwise scalar extension of the global augmented model has a quasi-isomorphic
underlying R-complex, compatibly with its augmentation.
Source: Stacks Project, Algebraization, Tags 099I and 099H.
(auxiliary; not a blueprint node).

Proof: take termwise scalar extension of K for L and its adjunction unit for u.
The canonical-unit comparison makes u a quasi-isomorphism. Define delta as the
adjoint of epsilon followed by the coefficient map R[0] to the restricted B[0].
The adjunction equation gives the required augmentation compatibility. The local
comparison is supplied by the quotient criterion, finite ordered Koszul homology,
and exact filtered colimits; no local description over B is needed in the conclusion.
-/
theorem exists_flat_ringedCech_baseChange
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (hK : HasLocalExtendedCechDescription R I.module I.inclusion K ε) :
    let r := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let rc := r.mapHomologicalComplex (.up ℤ)
    let σ : ringedSiteRingComplex R ⟶ rc.obj (ringedSiteRingComplex B) :=
      (HomologicalComplex.single _ (.up ℤ) 0).map
          (SheafOfModules.LocalizationCech.unitMap φ) ≫
        (HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app
          (SheafOfModules.unit (siteModuleRings B))
    ∃ (L : ringedSiteComplex B) (δ : L ⟶ ringedSiteRingComplex B)
      (u : K ⟶ rc.obj L), QuasiIso u ∧ u ≫ rc.map δ = ε ≫ σ := by
  dsimp only
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let rc := r.mapHomologicalComplex (.up ℤ)
  let σ : ringedSiteRingComplex R ⟶ rc.obj (ringedSiteRingComplex B) :=
    (HomologicalComplex.single _ (.up ℤ) 0).map
        (SheafOfModules.LocalizationCech.unitMap φ) ≫
      (HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app
        (SheafOfModules.unit (siteModuleRings B))
  exact augmented_model_of_adjunction
    (ringedScalarExtensionComplexAdjunction φ)
    K (ringedSiteRingComplex B) (ε ≫ σ)
    (flat_ringedCech_baseChange_data_quasiIso φ I hI hflat hquot K ε hK)

end CategoryTheory
