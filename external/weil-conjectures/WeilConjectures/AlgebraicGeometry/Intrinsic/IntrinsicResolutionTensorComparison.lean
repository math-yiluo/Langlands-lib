/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRealization

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationTensorComplex
import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.Additive

/-!
# Tensor cohomology under intrinsic coefficient realization

## References

* Stacks Project, Tags 00YV, 06YS and 06YU
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

private theorem acyclic_map_iff
    {C D : Type*} [Category.{v} C] [Category.{w} D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsEquivalence]
    (K : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic ↔ K.Acyclic := by
  constructor
  · intro h i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (h i)
    have hz' : IsZero (F.obj (K.homology i)) :=
      hz.of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K).symm
    apply (IsZero.iff_id_eq_zero _).2
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hz'
  · intro h i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    exact (F.map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1
      (h i))).of_iso ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K)

private theorem resolutionTensorTransportAux
    {C D : Type*} [Category.{v} C] [Category.{w} D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian.{v} C]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsEquivalence]
    (S : D ⥤ D ⥤ D) [S.PreservesZeroMorphisms]
    [∀ M, (S.obj M).PreservesZeroMorphisms]
    (hcomp : ∀ V W : CochainComplex C ℤ,
      Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor V W (curriedTensor C)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (.up ℤ)).obj V)
            ((F.mapHomologicalComplex (.up ℤ)).obj W) S))
    (K : _root_.DerivedCategory C) (L P : CochainComplex D ℤ)
    (eL : _root_.DerivedCategory.Q.obj L ≅ F.mapDerivedCategory.obj K)
    (f : P ⟶ L) (hf : QuasiIso f)
    (hP : ∀ V : CochainComplex D ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V P S).Acyclic)
    (N : C) (M : D) (eM : F.obj N ≅ M) :
    Nonempty (_root_.DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P
        ((HomologicalComplex.single D (.up ℤ) 0).obj M) S) ≅
      F.mapDerivedCategory.obj
        (K ⊗ (_root_.DerivedCategory.singleFunctor C 0).obj N)) := by
  classical
  let FC := F.mapHomologicalComplex (.up ℤ)
  let E := F.asEquivalence.mapHomologicalComplex (.up ℤ)
  let P' := E.inverse.obj P
  let eP : FC.obj P' ≅ P := E.counitIso.app P
  have hP' (V : CochainComplex C ℤ) (hV : V.Acyclic) :
      (CochainComplex.mapBifunctor V P' (curriedTensor C)).Acyclic := by
    apply (acyclic_map_iff F _).1
    obtain ⟨c⟩ := hcomp V P'
    let d := ((S.map₂CochainComplex.obj (FC.obj V))).mapIso eP
    intro i
    exact (hP (FC.obj V) ((acyclic_map_iff F V).2 hV) i).of_iso
      (c ≪≫ d).symm
  have hk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P' := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro V hV
    obtain ⟨V, rfl⟩ := V.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hV
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor V P' (curriedTensor C))).2 (hP' V hV)
    refine ⟨?_, hr⟩
    exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr
  have : QuasiIso f := hf
  let eq : F.mapDerivedCategory.obj (_root_.DerivedCategory.Q.obj P') ≅
      F.mapDerivedCategory.obj K :=
    F.mapDerivedCategoryFactors.app P' ≪≫ _root_.DerivedCategory.Q.mapIso eP ≪≫
      asIso (_root_.DerivedCategory.Q.map f) ≪≫ eL
  let ek : _root_.DerivedCategory.Q.obj P' ≅ K := F.mapDerivedCategory.preimageIso eq
  obtain ⟨c⟩ := hcomp P' ((HomologicalComplex.single C (.up ℤ) 0).obj N)
  let en : FC.obj ((HomologicalComplex.single C (.up ℤ) 0).obj N) ≅
      (HomologicalComplex.single D (.up ℤ) 0).obj M :=
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app N ≪≫
      (HomologicalComplex.single D (.up ℤ) 0).mapIso eM
  let et := ((S.map₂CochainComplex).mapIso eP).app _ ≪≫
    ((S.map₂CochainComplex).obj P).mapIso en
  let t := _root_.DerivedCategory.QObjTensorSingleFunctorObjIso P' hk N ≪≫
    _root_.DerivedCategory.Q.mapIso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) N P').symm
  exact ⟨_root_.DerivedCategory.Q.mapIso (c ≪≫ et).symm ≪≫
    (F.mapDerivedCategoryFactors.app _).symm ≪≫
    F.mapDerivedCategory.mapIso t.symm ≪≫
    F.mapDerivedCategory.mapIso (tensorIso ek (Iso.refl _))⟩

private theorem fixedDerivedTensor_obj
    (B : Type w) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})
    (K N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :
    ((ProEtale.derivedTensor B T).obj K).obj N = K ⊗ N := rfl

private theorem intrinsicDerivedTensor_obj
    (A : Type u) [CommRing A] (T : Scheme.{u})
    (L P W : CochainComplex
      (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) ℤ)
    (f : P ⟶ L) (hf : QuasiIso f) (hP : CochainComplex.IsAcyclicTensorKFlat P) :
    Scheme.derivedTensor T A L W P f hf hP =
      (letI := SheafOfModules.monoidalCategory (Scheme.proEtaleConstantRing T A)
       _root_.DerivedCategory.Q.obj (CochainComplex.mapBifunctor P W (curriedTensor _))) :=
  rfl

attribute [local instance] supportedSheaf_smallColimitsGeneric

local instance resolutionGenericSheafTensorTotal
    (B : Type w) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B] (T : Scheme.{u})
    (V W : CochainComplex (Sheaf (Scheme.ProEt.topology T) B) ℤ) :
    HomologicalComplex.HasMapBifunctor V W (curriedTensor _) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (supportedSheaf_smallColimitsGeneric B T) _ _) _

private theorem intrinsicResolutionHomologyAux
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (B : Type w) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (F : Sheaf (Scheme.ProEt.topology T) B ⥤
      Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsEquivalence]
    (hcomp : ∀ V W : CochainComplex
      (Sheaf (Scheme.ProEt.topology T) B) ℤ,
      letI := SheafOfModules.monoidalCategory (Scheme.proEtaleConstantRing T A)
      Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor V W (curriedTensor _)) ≅
          CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj V)
            ((F.mapHomologicalComplex (.up ℤ)).obj W) (curriedTensor _)))
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) B))
    (L P : CochainComplex
      (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) ℤ)
    (eL : _root_.DerivedCategory.Q.obj L ≅
      F.mapDerivedCategory.obj K)
    (f : P ⟶ L) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat P)
    (N : Sheaf (Scheme.ProEt.topology T) B)
    (M : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A))
    (eM : F.obj N ≅ M) (i : ℤ) :
    Nonempty
      ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (Scheme.derivedTensor T A L
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) P f hf hP) ≅
        F.obj
          ((_root_.DerivedCategory.homologyFunctor _ i).obj
            (((ProEtale.derivedTensor
              B T).obj K).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj N)))) := by
  rw [fixedDerivedTensor_obj, intrinsicDerivedTensor_obj]
  let := SheafOfModules.monoidalCategory (Scheme.proEtaleConstantRing T A)
  obtain ⟨e⟩ := resolutionTensorTransportAux F (curriedTensor _)
    hcomp K L P eL f hf hP N M eM
  exact ⟨(_root_.DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (F.mapDerivedCategoryHomologyFunctorIso i).symm.app _⟩

/-- Intrinsic K-flat tensor cohomology agrees with fixed-scalar derived tensor cohomology. -/
theorem intrinsic_resolution_tensor_homology_iso
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (L P : CochainComplex
      (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) ℤ)
    (eL : _root_.DerivedCategory.Q.obj L ≅
      (finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj K)
    (f : P ⟶ L) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat P)
    (N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (M : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A))
    (eM : (finiteCoefficientIntrinsicRealization T A).obj N ≅ M) (i : ℤ) :
    Nonempty
      ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (Scheme.derivedTensor T A L
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) P f hf hP) ≅
        (finiteCoefficientIntrinsicRealization T A).obj
          ((_root_.DerivedCategory.homologyFunctor _ i).obj
            (((ProEtale.derivedTensor
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj K).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj N)))) := by
  let : (finiteCoefficientIntrinsicRealization T A).IsEquivalence :=
    (finiteCoefficientIntrinsicRealization_exact T A).1
  exact intrinsicResolutionHomologyAux A T
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (finiteCoefficientIntrinsicRealization T A)
    (intrinsic_realization_tensor_complex_iso A T) K L P eL f hf hP N M eM i

end AlgebraicGeometry.ProEtale
