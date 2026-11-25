/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# Restriction of scalars along an isomorphism preserves K-flatness

Source: Stacks Project, Tags 06YN and 03ER.

Restricting the unit along an isomorphism of ring sheaves gives the unit, which is flat, so
`SheafOfModules.isKFlat_restrictScalars_of_flat` applies.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  {R B : Sheaf J CommRingCat.{max u v}}

/-- The unit restricted along an isomorphism of ring sheaves is the unit. -/
noncomputable def unitIsoRestrictScalarsUnit (φ : R ⟶ B) [IsIso φ] :
    unit ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) ≅
      (restrictScalars.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map φ)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj B)) := by
  let c := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).mapIso (asIso φ)
  apply (fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · exact (show (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj U ≃ₗ[
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj U]
        ((restrictScalars.{max u v} c.hom).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))).val.obj U from
      { toFun := c.hom.hom.app U
        invFun := c.inv.hom.app U
        left_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
          (congrArg (fun f ↦ f.hom) c.hom_inv_id) U) x
        right_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
          (congrArg (fun f ↦ f.hom) c.inv_hom_id) U) x
        map_add' := map_add _
        map_smul' := fun r x ↦ (c.hom.hom.app U).hom.map_mul r x }).toModuleIso
  · intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (c.hom.hom.naturality f) x

set_option synthInstance.maxSize 256 in
/-- Restriction of scalars along an isomorphism of ring sheaves preserves K-flatness. -/
theorem isKFlatTensor_restrictScalars_of_isIso (φ : R ⟶ B) [IsIso φ]
    (P : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj B)) ℤ)
    (hP : P.IsKFlatTensor) :
    CochainComplex.IsKFlatTensor ((Functor.mapHomologicalComplex (restrictScalars.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map φ))
        (ComplexShape.up ℤ)).obj P) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  have hunit : exactFunctor _ _ (tensorRight
      (unit ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))) :=
    ⟨preservesFiniteLimits_of_natIso (rightUnitorNatIso _).symm,
      preservesFiniteColimits_of_natIso (rightUnitorNatIso _).symm⟩
  have hres := (exactFunctor _ _).prop_of_iso
    ((curriedTensor _).flip.mapIso (unitIsoRestrictScalarsUnit φ)) hunit
  have hB : IsFlatOnSite (J := J) (R := R) ((restrictScalars.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map φ)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj B))) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm hres
  exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1
    (isKFlat_restrictScalars_of_flat φ hB P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP)).1

end SheafOfModules
