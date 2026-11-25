/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitAcyclic
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
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
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
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
import Mathlib.Algebra.Homology.QuasiIso
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
import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Derived direct image and strict tower limits

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0940
(blueprint: lem-weil-ringed-tower-pushforward-limit-comparison).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u w uA uB vA vB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

section Helpers

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

private theorem towerComparison_existsComposite
    {T : Type u} [Category T] [Abelian T] [HasDerivedCategory.{w} T]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : B ⥤ T) [F.Additive] [G.Additive]
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (RG : DerivedCategory.{w} B ⥤ DerivedCategory.{w} T)
    (ηf : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (ηg : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RG)
    (hf : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηf.app I))
    (hg : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (ηg.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :
    ∃ (η : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ (RF ⋙ RG)),
      (RF ⋙ RG).IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      ∀ X, η.app X = ηg.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        RG.map (ηf.app X) := by
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Gc := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let η : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (RF ⋙ RG) :=
    { app := fun X ↦ ηg.app (Fc.obj X) ≫ RG.map (ηf.app X)
      naturality := by
        intro X Y a
        change DerivedCategory.Q.map (Gc.map (Fc.map a)) ≫
            (ηg.app (Fc.obj Y) ≫ RG.map (ηf.app Y)) =
          (ηg.app (Fc.obj X) ≫ RG.map (ηf.app X)) ≫ RG.map (RF.map (DerivedCategory.Q.map a))
        have hn := ηg.naturality (Fc.map a)
        have hm := ηf.naturality a
        dsimp only [Functor.comp_map] at hn hm
        rw [← Category.assoc, hn]
        simp only [Category.assoc]
        rw [← RG.map_comp, hm, RG.map_comp] }
  refine ⟨η, ?_, fun _ ↦ rfl⟩
  apply (derives (F ⋙ G)).isRightDerivedFunctor_of_isIso η
  intro X
  have := hf X.obj X.property
  have := hg X.obj X.property
  change IsIso (ηg.app (Fc.obj X.obj) ≫ RG.map (ηf.app X.obj))
  infer_instance

variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

variable [HasLimitsOfShape ℕᵒᵖ A]

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem towerComparison_limPreservesKInjective
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes := by
  exact Adjunction.preservesKInjectiveComplexes
    (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⊣ lim)

private theorem towerComparison_existsLimitIso
    [HasLimitsOfShape ℕᵒᵖ B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (RT : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B))
    (LA : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (LB : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (ηf : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (ηt : ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RT)
    (ηA : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ LA)
    (ηB : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ LB)
    (hf : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηf.app I))
    (ht : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → IsIso (ηt.app I))
    (hA : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → IsIso (ηA.app I))
    (hB : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
      IsIso (ηB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)))
    (c : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
      (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)) :
    ∃ a : LA ⋙ RF ≅ RT ⋙ LB,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        ηf.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) ≫ RF.map (ηA.app X) ≫
          a.hom.app (DerivedCategory.Q.{w}.obj X) =
        DerivedCategory.Q.{w}.map
            ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app X) ≫
          ηB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) ≫ LB.map (ηt.app X) := by
  have := towerComparison_limPreservesKInjective (A := A)
  obtain ⟨α, hα, hαapp⟩ := towerComparison_existsComposite
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A) F LA RF ηA ηf hA (fun I hI ↦ by
      have := hI
      exact hf _ inferInstance)
  obtain ⟨β, hβ, hβapp⟩ := towerComparison_existsComposite
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
    RT LB ηt ηB ht hB
  have := hα
  have := hβ
  let τ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex c (ComplexShape.up ℤ))
    DerivedCategory.Q.{w}
  let a := Functor.rightDerivedNatIso (LA ⋙ RF) (RT ⋙ LB) α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) τ
  refine ⟨a, ?_⟩
  intro X
  have h := Functor.rightDerivedNatTrans_app (LA ⋙ RF) (RT ⋙ LB) α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) τ.hom X
  rw [hαapp, hβapp] at h
  rw [← Category.assoc]
  exact h

end Helpers

-- Repeated tower localizations and composite-unit equations require extra elaboration steps.
end CategoryTheory
