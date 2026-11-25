/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement

/-! A normalized natural transformation for sectionwise scalar extension.

## References

* Stacks 03EK and 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

-- The explicit generator calculation needs the larger elaboration budget.
/-- The sectionwise scalar extension admits a natural transformation normalized on generators. -/
theorem scalar_section_ordinary_normalized_map (T : Scheme.{u})
    (model : SectionModel a T) :
    ∃ ordinary : QuotientChange.extension a T ⋙
        (equivalence Λ' T).functor ⟶
      (equivalence Λ T).functor ⋙ model.E,
      ∀ (M : Modules Λ T) (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
        (((ordinary.app M) ≫ eqToHom (model.obj_eq _)).val.app W)
            (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m) =
          (toSheafify (Scheme.ProEt.topology T)
            (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T)
              ((equivalence Λ T).functor.obj M)).presheaf).app W
                ((1 : (ring Λ' T).obj.obj W)
                  ⊗ₜ[(ring Λ T).obj.obj W,
                    ((sectionQuotient a T).hom.app W).hom] m) := by
      let J := Scheme.ProEt.topology T
      let R := AlgebraicGeometry.ProEtale.condensedRingObj Λ T
      let S := AlgebraicGeometry.ProEtale.condensedRingObj Λ' T
      have hφ :
          CategoryTheory.InternalAbelianSheafModule.sectionScalarMap J
              (ProEtale.coefficientMap a T) = sectionQuotient a T := by
        rfl
      have hφsymm := hφ.symm
      cases hφ
      obtain ⟨pair, _, _, extension, hgen, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
        CategoryTheory.InternalAbelianSheafModule.internal_section_scalar_adjunction
          J (ProEtale.coefficientMap a T)
      let bridge : pair.extension ≅ model.E :=
        NatIso.ofComponents (fun M ↦
          eqToIso (by
            exact (pair.extension_obj M).trans (model.obj_eq M).symm)) (by
          intro M N f
          simp only [pair.extension_map, model.map_eq]
          dsimp [sectionQuotient,
            CategoryTheory.InternalAbelianSheafModule.sectionScalarMap]
          simp
          rfl)
      let ordinary := extension ≪≫
        Functor.isoWhiskerLeft (equivalence Λ T).functor bridge
      refine ⟨ordinary.hom, ?_⟩
      intro M W m
      have hg := hgen M W
        (show (condensedRingObj Λ' T).obj.obj W from
          (1 : (ring Λ' T).obj.obj W)) m
      let adj := Mod.extendRestrictAdjunction (ProEtale.coefficientMap a T)
      have hscalar (s : (ring Λ' T).obj.obj W) :
          InternalAbelianSheafModule.internalScalarGenerator J
              (ProEtale.coefficientMap a T) M W s m =
            s • (show ((equivalence Λ' T).functor.obj
              ((Mod.extendScalars (ProEtale.coefficientMap a T)).obj M)).val.obj W from
                (adj.unit.app M).hom.hom.app W m) := by
        have h := congrArg (fun f ↦ f.hom.app W)
          (Mod.whiskerLeft_extendUnitHom_smul' (ProEtale.coefficientMap a T) M)
        have hμ := congr_app (Functor.LaxMonoidal.μ_natural_right
          (sheafToPresheaf J AddCommGrpCat.{u + 1}) (condensedRingObj Λ' T)
            (Mod.extendUnitHom (ProEtale.coefficientMap a T) M)) W
        have hh := ConcreteCategory.congr_hom
          (congrArg (fun f ↦ f ≫
            (Mod.act ((Mod.extendScalars (ProEtale.coefficientMap a T)).obj M).X).hom.app W)
            hμ) (s ⊗ₜ[ℤ] m)
        change InternalAbelianSheafModule.internalScalarGenerator J
            (ProEtale.coefficientMap a T) M W s m = _
        change
          (((sheafToPresheaf J AddCommGrpCat.{u + 1}).obj (condensedRingObj Λ' T) ◁
            (sheafToPresheaf J AddCommGrpCat.{u + 1}).map
              (Mod.extendUnitHom (ProEtale.coefficientMap a T) M)).app W ≫
            ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u + 1})
              (condensedRingObj Λ' T) (Mod.extendScalarsObj
                (ProEtale.coefficientMap a T) M).X).app W) ≫
            (Mod.act (Mod.extendScalarsObj (ProEtale.coefficientMap a T) M).X).hom.app W)
            (s ⊗ₜ[ℤ] m) =
          (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u + 1})
              (condensedRingObj Λ' T) M.X).app W) ≫
            (S ◁ Mod.extendUnitHom (ProEtale.coefficientMap a T) M ≫
              Mod.act (Mod.extendScalarsObj (ProEtale.coefficientMap a T) M).X).hom.app W)
            (s ⊗ₜ[ℤ] m) at hh
        rw [h] at hh
        exact hh.symm
      have hunit :
          InternalAbelianSheafModule.internalScalarGenerator J
              (ProEtale.coefficientMap a T) M W
              (show (condensedRingObj Λ' T).obj.obj W from
                (1 : (ring Λ' T).obj.obj W)) m =
            ((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m := by
        rw [hscalar]
        simp [Mod.extendUnit_hom]
        rfl
      convert hg using 1 <;>
        simp [ordinary, bridge, J, sectionQuotient, hunit] <;> try rfl

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
