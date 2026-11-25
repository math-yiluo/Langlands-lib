/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The characterized second-factor localization map
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-map). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

/-- Exact scalar extension commutes with derived homology.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-second-localization-map). -/
noncomputable def flatDerivedHomologyIso
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} C)]
    (hflat : (algebraMap B C).Flat) (i : ℤ) :
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    (ModuleCat.extendScalars (algebraMap B C)).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} C) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙
        ModuleCat.extendScalars (algebraMap B C) := by
  let E := ModuleCat.extendScalars.{u} (algebraMap B C)
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let F := E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} C) i
  let G := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙ E
  let e₀ : E.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i ⋙ E :=
    NatIso.ofComponents (fun P ↦ (P.sc i).mapHomologyIso E)
      (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ i).map f) E)
  let e : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G :=
    Functor.isoWhiskerRight E.mapDerivedCategoryFactors _ ≪≫
      Functor.isoWhiskerLeft (E.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} C) i) ≪≫ e₀ ≪≫
        (Functor.isoWhiskerRight
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i) E).symm
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
      (DerivedCategory.Q ⋙ F) F := ⟨Iso.refl _⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
      (DerivedCategory.Q ⋙ G) G := ⟨Iso.refl _⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)) _ _ F G e

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

/-- Derive the ordinary scalar-extension associator using the target's universal counit.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-second-localization-map). -/
noncomputable def secondLocalizationDerivedMap
    (hflat : (algebraMap B Bp).Flat)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    L.derived ⋙ (ModuleCat.extendScalars (algebraMap B Bp)).mapDerivedCategory ⟶
      K.derived := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  letI := K.universal
  let E := ModuleCat.extendScalars.{u} (algebraMap B Bp)
  let β : DerivedCategory.Qh ⋙ (L.derived ⋙ E.mapDerivedCategory) ⟶
      (ModuleCat.extendScalars (algebraMap R Bp)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
    Functor.whiskerRight L.counit E.mapDerivedCategory ≫
      Functor.whiskerLeft
        ((ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ))
        E.mapDerivedCategoryFactorsh.hom ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
          ((ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B Bp)).symm ≪≫
            eqToIso (congrArg (fun f : R →+* Bp ↦ ModuleCat.extendScalars.{u} f)
              (IsScalarTower.algebraMap_eq R B Bp).symm)) (.up ℤ)).hom
          DerivedCategory.Qh
  exact K.derived.leftDerivedLift K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) _ β

/-- The underlying coefficient map on model cohomology is a concrete adjoint transpose.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-second-localization-map). -/
noncomputable def secondLocalizationCohomologyMap
    (hflat : (algebraMap B Bp).Flat)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) (i : ℤ) :
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj
        (L.cohomology i) ⟶
    (ModuleCat.restrictScalars.{u} (algebraMap B Bp)).obj
      ((ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).obj
          (K.cohomology i)) := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let E := ModuleCat.extendScalars.{u} (algebraMap B Bp)
  let X := DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
    ((restrict R A).obj Q))
  let β := E.map (L.cohomologyIso i).hom ≫
    (flatDerivedHomologyIso B Bp hflat i).inv.app (L.derived.obj X) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
        ((secondLocalizationDerivedMap R A B Bp D hflat Q L K).app X) ≫
          (K.cohomologyIso i).inv
  exact (ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)).homEquiv _ _ β

/-- This generator formula determines the D-linear map uniquely.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-second-localization-map). -/
def IsSecondLocalizationMap
    (hflat : (algebraMap B Bp).Flat)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) (i : ℤ)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i)) : Prop :=
  ∀ x : L.cohomology i,
    e ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x) =
      (1 : D) ⊗ₜ[A ⊗[R] Bp,algebraMap (A ⊗[R] Bp) D]
        (show K.cohomology i from
          secondLocalizationCohomologyMap R A B Bp D hflat Q L K i x)

include tRB in
/-- Equality on extension generators proves uniqueness of the characterized map.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-second-localization-map). -/
theorem IsSecondLocalizationMap.ext
    {hflat : (algebraMap B Bp).Flat}
    {Q : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D}
    {K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D} {i : ℤ}
    {e e' : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i)}
    (he : IsSecondLocalizationMap R A B Bp D hflat Q L K i e)
    (he' : IsSecondLocalizationMap R A B Bp D hflat Q L K i e') : e = e' := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (he x).trans (he' x).symm

end RingTensorCohomology
