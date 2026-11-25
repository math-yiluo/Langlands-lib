/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel
public import WeilConjectures.Algebra.Homology.Ringed.RingedSiteEquivalenceTensor
import all WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel

/-!
# Extension on the small model preserves flat K-flat complexes

## References

* Stacks Project, Categories, Tag 001J
* Stacks Project, Modules on Sites, Tags 03D1 and 03EL
* Stacks Project, Modules on Sites, Tags 03D1 and 06YN
* Stacks Tags 06YS, 03DI and 0E8I
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

open MonoidalCategory

/-- The inverse of an equivalence compatible with tensor products is compatible with
tensor products. -/
theorem nonempty_tensor_comp_inv_iso {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) :
    Nonempty (tensor D ⋙ F.inv ≅ F.inv.prod F.inv ⋙ tensor C) := by
  let E := F.asEquivalence
  let P := E.prod E
  exact ⟨isoWhiskerRight P.counitIso.symm (tensor D ⋙ F.inv) ≪≫
    isoWhiskerLeft P.inverse (isoWhiskerRight e.symm F.inv) ≪≫
    isoWhiskerLeft (P.inverse ⋙ tensor C) E.unitIso.symm⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- The small-model transport of module sheaves preserves the sheaf tensor product. -/
theorem sfCbcModelModules_tensor (X : Scheme.{t}) (A : Type t) [CommRing A] :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicConstantRing X A)
    letI := SheafOfModules.isMonoidal_W_independentCoefficients (sfCbcModelRing X A)
    letI := SheafOfModules.monoidalCategory (adicConstantRing X A)
    letI := SheafOfModules.monoidalCategory (sfCbcModelRing X A)
    Nonempty (MonoidalCategory.tensor _ ⋙ sfCbcModelModules X A ≅
      (sfCbcModelModules X A).prod (sfCbcModelModules X A) ⋙ MonoidalCategory.tensor _) := by
  have h := (sfCbcModelRingMap_existsUnique X A).exists.choose_spec.1
  let : IsIso (sfCbcModelRingMap X A) := h
  let e := (AsSmall.equiv.{t, t + 1, t + 1} (C := X.ProEt)).symm
  have : e.functor.IsContinuous (proEtaleModelTopology X) (ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsContinuous
      (proEtaleModelTopology X) (ProEt.topology X))
  have : e.inverse.IsContinuous (ProEt.topology X) (proEtaleModelTopology X) :=
    proEtaleModelUp_isContinuous X
  have := SheafOfModules.pushforward_equivalence_tensor_iso (proEtaleModelTopology X)
    (ProEt.topology X) e (adicConstantRing X A) (sfCbcModelRing X A)
    (asIso (sfCbcModelRingMap X A))
  unfold sfCbcModelModules
  exact this

/-- Small-model transport sends flat-term K-flat complexes to flat-term K-flat complexes. -/
theorem sfCbcModelModules_flat_kFlat (X : Scheme.{t}) (A : Type t) [CommRing A]
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X A) C)
    (hCf : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (adicConstantRing X A)) (C.X i))) :
    CochainComplex.IsKFlatTensor
        (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj C) ∧
      ∀ i : ℤ, SheafOfModules.IsFlat
        ((((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj C).X i) := by
  let R := adicConstantRing X A
  let S := sfCbcModelRing X A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  obtain ⟨q⟩ := sfCbcModelModules_tensor X A
  refine ⟨sfCbcKFlatTransport (sfCbcModelModules X A) q C hC, fun i ↦ ?_⟩
  exact sfCbcFlatTransport (sfCbcModelModules X A) q (C.X i) (hCf i)

/-- The inverse small-model transport sends flat-term K-flat complexes to flat-term K-flat
complexes. -/
theorem sfCbcModelModules_inverse_flat_kFlat (X : Scheme.{t}) (A : Type t) [CommRing A]
    (P : ConstantCompletion.Cx (sfCbcModelRing X A)) (hP : P.IsKFlatTensor)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X A)
        (((sfCbcModelModules X A).asEquivalence.inverse.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ i : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (adicConstantRing X A))
          ((((sfCbcModelModules X A).asEquivalence.inverse.mapHomologicalComplex
            (.up ℤ)).obj P).X i)) := by
  let R := adicConstantRing X A
  let S := sfCbcModelRing X A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  obtain ⟨q⟩ := sfCbcModelModules_tensor X A
  obtain ⟨q'⟩ := Functor.nonempty_tensor_comp_inv_iso (sfCbcModelModules X A) q
  let G := (sfCbcModelModules X A).asEquivalence.inverse
  have : G.Additive := CategoryTheory.Equivalence.inverse_additive _
  refine ⟨sfCbcKFlatTransport G q' P hP, fun i ↦ ?_⟩
  exact sfCbcFlatTransport G q' (P.X i) (hf i)

/-- Ordinary extension preserves flat-term K-flat complexes. -/
theorem sfCbcOpenExtension_flat_kFlat {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A]
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing U A)) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing U A) C)
    (hCf : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (adicConstantRing U A)) (C.X i))) :
    CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X A)
        (((sfCbcOpenExtension j A).mapHomologicalComplex (.up ℤ)).obj C) ∧
      ∀ i : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (adicConstantRing X A))
          ((((sfCbcOpenExtension j A).mapHomologicalComplex (.up ℤ)).obj C).X i)) := by
  let W := cbcOpenObject j inferInstance
  let F : SheafOfModules.{t + 1} (adicModuleRing U A) ⥤
      SheafOfModules.{t + 1} ((adicModuleRing X A).over W) :=
    sfCbcConstantModuleToSlice X W A
  let G : SheafOfModules.{t + 1} ((adicModuleRing X A).over W) ⥤
      SheafOfModules.{t + 1} (adicModuleRing X A) :=
    SheafOfModules.localizedModuleExtension.{t} (adicConstantRing X A) W
  have hF : F.Additive := sfCbcSliceTransport_additive X W A
  have hG : G.Additive := SheafOfModules.localizedModuleExtension_additive
    (adicConstantRing X A) W
  let P := (F.mapHomologicalComplex (.up ℤ)).obj C
  obtain ⟨hP, hflat⟩ := sfCbcSliceTransportKFlat X W A C hC hCf
  obtain ⟨hk, hf, _⟩ := SheafOfModules.ringedOpen_preserves_flat_resolution.{t + 1, t, t + 1}
    (adicConstantRing X A) W
  refine ⟨sfCbcMapComplexCompProp F G (_hF := hF) (_hG := hG) C
      (fun T ↦ CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X A) T)
      (hk P hP), fun i ↦ ?_⟩
  apply sfCbcMapComplexCompProp F G (_hF := hF) (_hG := hG) C
    (fun T ↦ CategoryTheory.exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (adicConstantRing X A)) (T.X i)))
  let T := (G.mapHomologicalComplex (.up ℤ)).obj P
  exact (CategoryTheory.exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (adicConstantRing X A) (T.X i)) (hf P hflat i)

/-- Termwise extension on the small model preserves flat-term K-flat complexes. -/
theorem sfCbcModelExtension_flat_kFlat {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A]
    (P : ConstantCompletion.Cx (sfCbcModelRing U A)) (hP : P.IsKFlatTensor)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsKFlatTensor
      (((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat
        ((((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P).X q) := by
  let G := (sfCbcModelModules U A).asEquivalence.inverse
  have : G.Additive := CategoryTheory.Equivalence.inverse_additive _
  let Q : ConstantCompletion.Cx (sfCbcModelRing X A) → Prop := fun T ↦
    CochainComplex.IsKFlatTensor T ∧ ∀ q : ℤ, SheafOfModules.IsFlat (T.X q)
  obtain ⟨h₁, h₁f⟩ := sfCbcModelModules_inverse_flat_kFlat U A P hP hf
  obtain ⟨h₂, h₂f⟩ := sfCbcOpenExtension_flat_kFlat j A _ h₁ h₁f
  have h₃ : Q _ := sfCbcModelModules_flat_kFlat X A _ h₂ h₂f
  have h₄ := sfCbcMapComplexCompProp (sfCbcOpenExtension j A) (sfCbcModelModules X A) _ Q h₃
  have h₅ := sfCbcMapComplexCompProp G (sfCbcOpenExtension j A ⋙ sfCbcModelModules X A) P Q h₄
  exact h₅

end AlgebraicGeometry.Scheme
