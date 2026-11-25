/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionIdentityTotalTensor
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorEdgeRepresentativeEquation
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
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
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

set_option linter.privateModule false

/-! Field-level coherence law for normalized ringed projection tensor comparisons.
(blueprint: lem-sfb-ringed-projection-tensor-laws-identity-law) -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace SheafOfModules.ProjectionCoherence

set_option synthInstance.maxSize 2048

private noncomputable abbrev tensorTotal (X : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj ((@MonoidalCategory.curriedTensor X.mateModules _
    (monoidalCategory X.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

private noncomputable abbrev pull {X : RingedTensorCorner.{u, w}}
    (h : RingedTensorEdge X X) := h.pullback.mapHomologicalComplex (.up ℤ)

private theorem pull_good {X : RingedTensorCorner.{u, w}}
    (h : RingedTensorEdge X X) {P : CochainComplex X.mateModules ℤ} (hp : X.mateFlat P) :
    X.mateFlat ((pull h).obj P) := by
  have hp' : ∀ n, IsFlatOnSite (J := X.topology) (R := X.ring) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso X.ring _).symm (hp.2 n)
  obtain ⟨hk, hf⟩ := isKFlat_ringedToposPullback h.inverse h.direct h.adjunction
    h.algebraic h.ringMap h.pullback h.object_eq h.map_eq P hp.1 hp'
  exact ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso X.ring _) (hf n)⟩

private theorem total_good {X : RingedTensorCorner.{u, w}}
    {P Q : CochainComplex X.mateModules ℤ} (hp : X.mateFlat P) (hq : X.mateFlat Q) :
    X.mateFlat ((tensorTotal X).obj (P, Q)) := by
  have ht := KFlatTotalTensorModel.kFlat_total_tensor_model X.ring P Q hp.1 hq.1
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso X.ring _).symm (hp.2 n))
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso X.ring _).symm (hq.2 n))
  exact ⟨ht.1, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso X.ring _) (ht.2.1 n)⟩

private theorem tensor_map_comp {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ B) {P₁ P₂ P₃ Q₁ Q₂ Q₃ : A}
    (a : P₁ ⟶ P₂) (b : Q₁ ⟶ Q₂) (c : P₂ ⟶ P₃) (d : Q₂ ⟶ Q₃) :
    T.map (Prod.mkHom (a ≫ c) (b ≫ d)) =
      T.map (Prod.mkHom a b) ≫ T.map (Prod.mkHom c d) :=
  T.map_comp (Prod.mkHom a b) (Prod.mkHom c d)

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso
  RingedTensorEdge.tensorComparison ringedTopoiCanonicalDerivedTensorComparison
  derivedPullbackComplexComparison

end SheafOfModules.ProjectionCoherence
