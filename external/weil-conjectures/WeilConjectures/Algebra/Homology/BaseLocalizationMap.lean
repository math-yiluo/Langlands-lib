/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The canonical map for localization of the tensor base

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-base-localization-map).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R Rp B : Type u) [CommRing R] [CommRing Rp] [CommRing B]
  [Algebra R Rp] [Algebra R B] [Algebra Rp B] [IsScalarTower R Rp B]

/-- The ordinary tensor identification, fixed on pure tensors.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-map). -/
noncomputable def baseLocalizationTensorIso (S : Submonoid R) [IsLocalization S Rp] :
    ModuleCat.restrictScalars.{u} (algebraMap R Rp) ⋙
        ModuleCat.extendScalars (algebraMap R B) ≅
      ModuleCat.extendScalars (algebraMap Rp B) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · have ht := IsScalarTower.algebraMap_eq R Rp B
    let : Algebra R B := (algebraMap R B).toAlgebra
    let : Algebra Rp B := (algebraMap Rp B).toAlgebra
    let : IsScalarTower R Rp B := IsScalarTower.of_algebraMap_eq' ht
    let : Module R M := Module.compHom M (algebraMap R Rp)
    let : IsScalarTower R Rp M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let := IsLocalization.tensorProduct_compatibleSMul S Rp B M
    exact (TensorProduct.equivOfCompatibleSMul R Rp B B M).symm.toModuleIso
  · intro M N f
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rfl

variable (A D : Type u) [CommRing A] [CommRing D]
  [Algebra R A] [Algebra Rp A] [IsScalarTower R Rp A]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- The counit for the restricted derived model followed by ordinary localization.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-map). -/
noncomputable def baseLocalizationCounit (S : Submonoid R) [IsLocalization S Rp]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D) :
    DerivedCategory.Qh ⋙
        (ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapDerivedCategory ⋙ L.derived ⟶
      (ModuleCat.extendScalars (algebraMap Rp B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapDerivedCategoryFactorsh.hom
      L.derived ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapHomotopyCategory (.up ℤ))
      L.counit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (baseLocalizationTensorIso R Rp B S) (.up ℤ)).hom
      DerivedCategory.Qh

/-- Universal lift of the localized counit. It involves no arbitrary existence witness.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-map). -/
noncomputable def baseLocalizationDerivedMap (S : Submonoid R) [IsLocalization S Rp]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) :
    (ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapDerivedCategory ⋙ L.derived ⟶
      K.derived := by
  let := K.universal
  exact K.derived.leftDerivedLift K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} Rp) (.up ℤ)) _
    (baseLocalizationCounit R Rp B A D S Q L)

/-- The restriction input identification as a natural isomorphism.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-map). -/
noncomputable def baseLocalizationInputNatIso :
    restrict R A ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙
        DerivedCategory.Qh ≅
      (restrict Rp A ⋙ HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
      (ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapDerivedCategory := by
  let r := ModuleCat.restrictScalars.{u} (algebraMap R Rp)
  let c := ModuleCat.restrictScalarsComp' (algebraMap R Rp) (algebraMap Rp A)
    (algebraMap R A) (IsScalarTower.algebraMap_eq R Rp A)
  let z := (Functor.mapHomologicalComplexCompIso c.symm (.up ℤ)).symm
  exact isoWhiskerRight z
      (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (restrict Rp A)
      (isoWhiskerRight (r.mapHomotopyCategoryFactors (.up ℤ)).symm DerivedCategory.Qh) ≪≫
    isoWhiskerLeft (restrict Rp A) (Functor.associator _ _ _) ≪≫
    isoWhiskerLeft (restrict Rp A)
      (isoWhiskerLeft (HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ))
        r.mapDerivedCategoryFactorsh.symm) ≪≫
    isoWhiskerLeft (restrict Rp A) (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The identity of inputs in the chosen derived categories.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-map). -/
noncomputable def baseLocalizationInputIso
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj ((restrict R A).obj Q)) ≅
      (ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).obj
            ((restrict Rp A).obj Q))) :=
  (baseLocalizationInputNatIso R Rp A).app Q

/-- The canonical B-linear cohomology map used to characterize the D-linear map.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-map). -/
noncomputable def baseLocalizationCohomologyMap (S : Submonoid R) [IsLocalization S Rp]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) (i : ℤ) :
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj
        (L.cohomology i) ⟶
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom).obj
        (K.cohomology i) :=
  (L.cohomologyIso i).hom ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      (L.derived.map (baseLocalizationInputIso R Rp A Q).hom ≫
        (baseLocalizationDerivedMap R Rp B A D S Q L K).app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).obj
              ((restrict Rp A).obj Q)))) ≫
    (K.cohomologyIso i).inv

/-- A generator equation determining the localized map uniquely.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-map). -/
def IsBaseLocalizationMap (S : Submonoid R) [IsLocalization S Rp]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) (i : ℤ)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).obj (K.cohomology i)) : Prop :=
  ∀ x : L.cohomology i,
    e ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x) =
      (1 : D) ⊗ₜ[A ⊗[Rp] B,algebraMap (A ⊗[Rp] B) D]
        (baseLocalizationCohomologyMap R Rp B A D S Q L K i x)

/-- Generator uniqueness, including the zero coefficient ring.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-map). -/
theorem IsBaseLocalizationMap.ext (S : Submonoid R) [IsLocalization S Rp]
    {Q : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D}
    {K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D} {i : ℤ}
    {e e' : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).obj (K.cohomology i)}
    (he : IsBaseLocalizationMap R Rp B A D S Q L K i e)
    (he' : IsBaseLocalizationMap R Rp B A D S Q L K i e') : e = e' := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (he x).trans (he' x).symm

end RingTensorCohomology

