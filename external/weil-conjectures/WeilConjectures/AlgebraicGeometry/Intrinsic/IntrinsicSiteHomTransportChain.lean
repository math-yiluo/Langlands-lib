/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationTensorComplex
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Chain-level intrinsic Hom transport

## References

* Stacks Project, Tags 00YV, 08J7 and 0A95
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

private noncomputable def transportRightAdjoint
    {C D : Type*} [Category C] [Category D] (E : C ≌ D)
    {T H : C ⥤ C} {S K : D ⥤ D} (a : T ⊣ H) (b : S ⊣ K)
    (e : T ⋙ E.functor ≅ E.functor ⋙ S) :
    H ⋙ E.functor ≅ E.functor ⋙ K := by
  let d : E.inverse ⋙ T ≅ S ⋙ E.inverse :=
    ((Functor.associator E.inverse T E.functor) ≪≫ e.inverseCompIso).isoCompInverse
  exact conjugateIsoEquiv (E.symm.toAdjunction.comp a)
    (b.comp E.symm.toAdjunction) d.symm

-- Tensor compatibility alone suffices here; no monoidal coherence choices are needed.
private noncomputable def transportComplexHom
    {C D : Type*} [Category.{v} C] [Category.{w} D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
    [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (L I : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.internalHomObj L I) ≅
      CochainComplex.internalHomObj ((F.mapHomologicalComplex (.up ℤ)).obj L)
        ((F.mapHomologicalComplex (.up ℤ)).obj I) := by
  let E := F.asEquivalence.mapHomologicalComplex (.up ℤ)
  let τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) :=
    { app := fun X ↦
        { app := fun Y ↦ e.hom.app (X, Y)
          naturality := by
            intro Y Y' g
            simpa using e.hom.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, g) }
      naturality := by
        intro X X' f
        ext Y
        simpa using e.hom.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) }
  have (X Y : C) : IsIso ((τ.app X).app Y) := (e.app (X, Y)).isIso_hom
  let t : tensorLeft L ⋙ E.functor ≅ E.functor ⋙ tensorLeft (E.functor.obj L) :=
    asIso ((HomologicalComplex.mapBifunctorComparisonNatTrans τ (.up ℤ)).app L)
  exact (transportRightAdjoint E (CochainComplex.tensorHomAdjunction L)
    (CochainComplex.tensorHomAdjunction (E.functor.obj L)) t).app I

namespace AlgebraicGeometry.ProEtale

private noncomputable def fixedHomRepresentative
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (L I : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    [I.IsKInjective] :
    (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
      (op (DerivedCategory.Q.obj L))).obj (DerivedCategory.Q.obj I)) ≅
      DerivedCategory.Q.obj (CochainComplex.internalHomObj L I) := by
  let C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  letI : HasColimitsOfSize.{0, 0} C := Scheme.ProEt.sheafModuleHasCountableColimits A X
  letI (V W : GradedObject ℤ C) : V.HasTensor W :=
    fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
      (@HasColimitsOfSize.has_colimits_of_shape _ _
        (Scheme.ProEt.sheafModuleHasCountableColimits A X) _ _) _
  letI (V W Y Z : GradedObject ℤ C) : GradedObject.HasTensor₄ObjExt V W Y Z :=
    inferInstance
  letI (V W Y : GradedObject ℤ C) : GradedObject.HasGoodTensor₁₂Tensor V W Y :=
    inferInstance
  letI (V W Y : GradedObject ℤ C) : GradedObject.HasGoodTensorTensor₂₃ V W Y :=
    inferInstance
  letI : IsGrothendieckAbelian.{u + 1} C :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ X
  letI : HasColimitsOfShape ℤ C := inferInstance
  letI : HasExactColimitsOfShape ℤ C := hasExactColimitsOfShape_int C
  letI (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) := inferInstance
  letI (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) := inferInstance
  letI : Abelian.HasFunctorialFlatResolution C :=
    hasFunctorialFlatResolution_sheaf (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  letI (j : ℤ) : HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) C :=
    @HasColimitsOfSize.has_colimits_of_shape _ _
      (Scheme.ProEt.sheafModuleHasCountableColimits A X) _ _
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  letI : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.IsLeftDerivabilityStructure :=
    Λ.reduced.homotopyCategory_kFlat_isLeftDerivabilityStructure
      ObjectProperty.flat.essImage_ι_le
  let P := (HomotopyCategory.quotient C (.up ℤ)).obj L
  let e : DerivedCategory.Qh.obj P ≅ DerivedCategory.Q.obj L :=
    (DerivedCategory.quotientCompQhIso C).app L
  let a := (DerivedCategory.tensorHomAdjunctionQhObj P).ofNatIsoLeft
    ((tensoringLeft _).mapIso e)
  let d := Adjunction.rightAdjointUniq (derivedTensorHomAdjunction _ _) a
  have : IsIso ((DerivedCategory.internalHomQhObjUnit P).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I)) := by
    infer_instance
  exact d.app (DerivedCategory.Q.obj I) ≪≫
    (DerivedCategory.internalHomQhObj P).mapIso
      ((DerivedCategory.quotientCompQhIso C).app I).symm ≪≫
    (asIso ((DerivedCategory.internalHomQhObjUnit P).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotientCompInternalHomIso P).app I) ≪≫
    (DerivedCategory.quotientCompQhIso C).app (CochainComplex.internalHomObj L I)

/-- The realized fixed-coefficient derived Hom is represented by the intrinsic
Hom complex on the chosen K-injective representatives. -/
theorem intrinsicSiteHom_transport_chain (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (Lc Ic : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    [Ic.IsKInjective] :
    Nonempty
      ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
            (op (DerivedCategory.Q.obj Lc))).obj (DerivedCategory.Q.obj Ic)) ≅
        DerivedCategory.Q.obj
          (homComplex.{u + 1, u, u + 1, u + 1}
            (R := proEtaleConstantRing X A)
            (((finiteCoefficientIntrinsicRealization X A).mapHomologicalComplex
              (.up ℤ)).obj Lc)
            (((finiteCoefficientIntrinsicRealization X A).mapHomologicalComplex
              (.up ℤ)).obj Ic))) := by
  let C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let R := proEtaleConstantRing X A
  let D := proEtaleRingModules X R
  let F := finiteCoefficientIntrinsicRealization X A
  let : F.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact X A).1
  let : MonoidalCategory D := SheafOfModules.monoidalCategory R
  let : SymmetricCategory D := SheafOfModules.symmetricCategory R
  let : MonoidalClosed D :=
    WeilConjectures.ZeroClassAux.moduleMonoidalClosed.{u + 1, u + 1, u} R
  let : HasLimitsOfSize.{0, 0} C := hasLimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let : HasColimitsOfSize.{0, 0} C := Scheme.ProEt.sheafModuleHasCountableColimits A X
  let : HasLimitsOfSize.{0, 0} D := hasLimitsOfSizeShrink.{0, 0, u + 1, u + 1} D
  let : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} D
  obtain ⟨t⟩ := intrinsicTensorNatIso X A
  let c := transportComplexHom F t Lc Ic
  let h := WeilConjectures.ZeroClassAux.homComplexIsoInternalHomObj.{u + 1, u + 1, u}
    (R := R) ((F.mapHomologicalComplex (.up ℤ)).obj Lc)
      ((F.mapHomologicalComplex (.up ℤ)).obj Ic)
  exact ⟨F.mapDerivedCategory.mapIso (fixedHomRepresentative X A Lc Ic) ≪≫
    F.mapDerivedCategoryFactors.app (CochainComplex.internalHomObj Lc Ic) ≪≫
    DerivedCategory.Q.mapIso (c ≪≫ h.symm)⟩

end AlgebraicGeometry.ProEtale
