/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-! # Derived extension and restriction of global scalars
Source: Stacks Project, Tag 0AA7.
(blueprint: lem-sc-mixed-global-extension-adjunction).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry

variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- The normalized derived extension/restriction adjunction.
Source: Stacks Tag 0AA7, computed on K-flat resolutions.
(blueprint: lem-sc-mixed-global-extension-adjunction). -/
theorem mixedGlobalExtension_adjunction {R B : Type u} [CommRing R] [CommRing B]
    (ρ : R →+* B) :
    ∃ E : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B),
      Nonempty (E ⊣ (ModuleCat.restrictScalars.{u} ρ).mapDerivedCategory) := by
  have : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
  have : (ModuleCat.extendScalars.{u, u, u} ρ).PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ α hα
    let N := (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).obj (𝟙_ _)
    have h := (CochainComplex.mixedTensor_kFlat_quasiIso ρ).1 N P Q α hα hP hQ
    let e := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor ρ).flip (𝟙_ (ModuleCat.{u} B))
    have h' : QuasiIso
        ((((ModuleCat.mixedTensor ρ).obj (𝟙_ (ModuleCat.{u} B))).mapHomologicalComplex
          (.up ℤ)).map α) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality α).symm)).1 h
    let e₀ : (ModuleCat.mixedTensor ρ).obj (𝟙_ (ModuleCat.{u} B)) ≅
        ModuleCat.extendScalars.{u, u, u} ρ :=
      Functor.isoWhiskerLeft (ModuleCat.extendScalars ρ)
        (leftUnitorNatIso (ModuleCat.{u} B)) ≪≫ Functor.rightUnitor _
    let e₁ := NatIso.mapHomologicalComplex e₀ (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e₁.app P) (e₁.app Q) (e₁.hom.naturality α).symm)).1 h'
  refine ⟨(ModuleCat.extendScalars.{u, u, u} ρ).leftDerivedFunctor, ⟨?_⟩⟩
  exact (ModuleCat.extendRestrictScalarsAdj ρ).derivedAdjunction.ofNatIsoRight
    (ModuleCat.restrictScalars.{u} ρ).rightDerivedFunctorIsoMapDerivedCategory

/-- Derived extension of global scalars. Source: Stacks Tag 0AA7. -/
def mixedGlobalExtension {T S : Scheme.{u}} (g : T ⟶ S) :=
  Classical.choose (mixedGlobalExtension_adjunction g.appTop.hom)

/-- The extension/restriction adjunction for the global rings. Source: Stacks Tag 0AA7. -/
def mixedGlobalExtensionAdjunction {T S : Scheme.{u}} (g : T ⟶ S) :
    mixedGlobalExtension g ⊣ schemeGlobalScalarRestriction g :=
  Classical.choice (Classical.choose_spec (mixedGlobalExtension_adjunction g.appTop.hom))

end AlgebraicGeometry
