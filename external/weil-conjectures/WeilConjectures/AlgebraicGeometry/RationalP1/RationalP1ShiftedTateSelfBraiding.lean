/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1StrengthProjectionAction
import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.ConstructibleSheaf.LisseRankOne
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.GroupTheory.Torsion
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
import WeilConjectures.AlgebraicGeometry.TorsionAssembly
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import Mathlib.Tactic.SuppressCompilation
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair

/-! The self-symmetry of the even shifted rational Tate line.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] twist projectionMap tensorShiftIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

open Opposite

attribute [local implicit_reducible]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Monoidal.induced
  Sheaf.monoidalCategory Sheaf.symmetricCategory Sheaf.braidedCategory

attribute [local instance 20000] Sheaf.monoidalCategory
  Sheaf.symmetricCategory Sheaf.braidedCategory
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

private local instance internal_comm
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    @IsCommMonObj _ _ _ (inferInstance : SymmetricCategory
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
      (condensedRingObj Λ X) _ := by
  exact isCommMonObj_condensedRingObj Λ X

private local instance internal_braided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    BraidedCategory (Modules Λ X) := by
  exact (Mod.braidedCategory
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (R := condensedRingObj Λ X))

private local instance internal_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalClosed (Modules Λ X) := by
  exact (Mod.monoidalClosed
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (R := condensedRingObj Λ X))

private local instance internal_resolution
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Modules Λ X) := by
  exact (Mod.hasFunctorialFlatResolution
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (R := condensedRingObj Λ X))

private theorem section_line_self_braiding
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [M.IsFiniteLocallyFreeOfRank 1] : (β_ M M).hom = 𝟙 _ := by
  classical
  obtain ⟨I, U, hU, hM⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := M) (r := 1)).mp inferInstance
  have charts (i : I) : M.over (U i) ≅ SheafOfModules.unit
      (((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (U i)) :=
    (hM i).some ≪≫ SheafOfModules.freeUniqueIso (ULift.{u + 1} (Fin 1))
  apply SheafOfModules.LineEvaluation.pure_hom_ext.{u + 1, u, u + 1} R M M (M ⊗ M)
  intro V x y
  rw [SheafOfModules.LineEvaluation.pure_braiding.{u + 1, u, u + 1}]
  change SheafOfModules.LineEvaluation.pureTensor.{u + 1, u, u + 1} R M M V y x =
    SheafOfModules.LineEvaluation.pureTensor.{u + 1, u, u + 1} R M M V x y
  apply SheafOfModules.LineEvaluation.section_ext.{u + 1, u, u + 1} R (M ⊗ M) _ _
    (Sieve.ofObjects U V.unop) (hU V.unop)
  intro W f hf
  rcases hf with ⟨i, ⟨g⟩⟩
  rw [SheafOfModules.LineEvaluation.pure_restrict.{u + 1, u, u + 1},
    SheafOfModules.LineEvaluation.pure_restrict.{u + 1, u, u + 1}]
  obtain ⟨p, _, _, _, hp⟩ :=
    SheafOfModules.LineEvaluation.chart_basis.{u + 1, u, u + 1} R M (U i) (charts i)
  obtain ⟨a, ha⟩ := hp (Over.mk g) (M.val.map f.op x)
  obtain ⟨b, hb⟩ := hp (Over.mk g) (M.val.map f.op y)
  let : Module (R.obj.obj (op W)) ((M ⊗ M).val.obj (op W)) :=
    ModuleCat.isModule ((M ⊗ M).val.obj (op W))
  rw [ha, hb, SheafOfModules.LineEvaluation.pure_smul_left.{u + 1, u, u + 1},
    SheafOfModules.LineEvaluation.pure_smul_left.{u + 1, u, u + 1},
    SheafOfModules.LineEvaluation.pure_smul_right.{u + 1, u, u + 1},
    SheafOfModules.LineEvaluation.pure_smul_right.{u + 1, u, u + 1},
    smul_smul, smul_smul, mul_comm]

private theorem line_flat_and_braiding
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
    ObjectProperty.flat (line l c X) ∧
      (β_ (line l c X) (line l c X)).hom = 𝟙 _ := by
  classical
  let R := condensedRingObj (coefficient l c).X X
  let : MonObj R := inferInstanceAs (MonObj (condensedRingObj (coefficient l c).X X))
  let : IsCommMonObj R :=
    isCommMonObj_condensedRingObj (coefficient l c).X X
  let E := InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X) R
  let M := E.functor.obj (line l c X)
  have hM : M.IsFiniteLocallyFreeOfRank 1 := by
    dsimp only [M, E, R]
    cases c with
    | none =>
      convert! (transparency := .all)
        (spTwists_locallyFree X l (Classical.arbitrary _)).2.2 using 1
    | some F =>
      convert! (transparency := .all) (spTwists_locallyFree X l F).2.1 using 1
  let := hM
  constructor
  · apply (InternalAbelianSheafModule.flat_iff_sectionModule
      (Scheme.ProEt.topology X) R (line l c X)).2
    change SheafOfModules.IsFlatOnSite M
    simpa only [SheafOfModules.IsFlatOnSite, exactFunctor_iff,
      WeilConjectures.coefficientTwistLine,
      WeilConjectures.coefficientTwistPower,
      SheafOfModules.scalarTensorPower] using
      (WeilConjectures.coefficientTwistLine_exact X M 1).2
  · obtain ⟨_, e, _, _, _, _, _, _, _, hb, _⟩ :=
      InternalAbelianSheafModule.internal_section_tensor_comparison
        (Scheme.ProEt.topology X) R
    apply E.functor.map_injective
    apply (cancel_mono (e (line l c X) (line l c X)).hom).1
    have hb' : E.functor.map (β_ (line l c X) (line l c X)).hom ≫
        (e (line l c X) (line l c X)).hom =
        (e (line l c X) (line l c X)).hom ≫ (β_ M M).hom := by
      convert! (transparency := .all) (hb (line l c X) (line l c X)).symm using 1
    refine hb'.trans ?_
    rw [section_line_self_braiding X _ M]
    exact (Category.comp_id _).trans
      ((congrArg (fun k ↦ k ≫ (e (line l c X) (line l c X)).hom)
        (E.functor.map_id (line l c X ⊗ line l c X))).trans
          (Category.id_comp _)).symm

/-- The native Koszul braiding of the positive Tate line shifted by two with itself
is identity wherever l is invertible. -/
theorem shifted_tate_self_braiding
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
    let T := (((DerivedCategory.singleFunctor (Modules (coefficient l c).X X) 0).obj
      (line l c X)) ⟦(2 : ℤ)⟧)
    (tensorBraiding (coefficient l c).X X T T).hom = 𝟙 (T ⊗ T) := by
  obtain ⟨hf, hb⟩ := line_flat_and_braiding l c X
  unfold tensorBraiding internalMonoidal internalTensorBundle nativeTensorBundle
  exact Etale.CoordinateTrace.evenShiftCanonicalSelfSymmetry (line l c X) hf hb 1

end AlgebraicGeometry.ProEtale.RationalP1
