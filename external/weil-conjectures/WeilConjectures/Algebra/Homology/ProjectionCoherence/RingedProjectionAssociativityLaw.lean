/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
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
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.DerivedPullbackRepresentativeComputationSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement

set_option linter.privateModule false

/-! Field-level coherence law for normalized ringed projection tensor comparisons.
(blueprint: lem-sfb-ringed-projection-tensor-laws-associativity-law) -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Functor
namespace SheafOfModules.ProjectionCoherence

private abbrev Modules (A : RingedTensorCorner.{u, w}) :=
  SheafOfModules.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

private abbrev Complexes (A : RingedTensorCorner.{u, w}) := CochainComplex (Modules A) ℤ

private abbrev Good {A : RingedTensorCorner.{u, w}} (P : Complexes A) : Prop :=
  P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

private noncomputable abbrev totalTensor (A : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj ((@MonoidalCategory.curriedTensor (Modules A) _
    (monoidalCategory A.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

private noncomputable abbrev pull {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) := e.pullback.mapHomologicalComplex (.up ℤ)

private noncomputable abbrev comparison {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P : Complexes A) :=
  derivedPullbackComplexComparison e.pullback e.left e.epsilon P

private noncomputable abbrev delta {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P Q : Complexes A) :
    (pull e).obj ((totalTensor A).obj (P, Q)) ⟶
      (totalTensor B).obj ((pull e).obj P, (pull e).obj Q) :=
  (e.ordinaryTensor.totalIso A.ring B.ring e.inverseRing e.inverse e.algebraic e.ringMap
    e.pullback e.object_eq e.pushforward e.moduleAdjunction P Q).inv

private theorem pull_good {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P : Complexes A} (hp : Good P) :
    Good ((pull e).obj P) := by
  have hp' : ∀ n, IsFlatOnSite (J := A.topology) (R := A.ring) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso A.ring _).symm (hp.2 n)
  obtain ⟨hk, hf⟩ := isKFlat_ringedToposPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq P hp.1 hp'
  exact ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso B.ring _) (hf n)⟩

private theorem total_good {A : RingedTensorCorner.{u, w}}
    {P Q : Complexes A} (hp : Good P) (hq : Good Q) :
    Good ((totalTensor A).obj (P, Q)) := by
  have ht := KFlatTotalTensorModel.kFlat_total_tensor_model A.ring P Q hp.1 hq.1
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hp.2 n))
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hq.2 n))
  exact ⟨ht.1, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso A.ring _) (ht.2.1 n)⟩

private theorem comparison_isIso {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P : Complexes A} (hp : Good P) :
    IsIso (comparison e P) := by
  exact (CanonicalTensorPullbackOfUniverses.derivedPullback_kflat_tensor_computation
    e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq e.left e.epsilon e.isLeftDerived).1
    P hp.1 (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hp.2 n))

-- Elaborate the uniquely characterized comparison with both tensor models fixed.
private theorem edge_equation {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (a : RingedTensorModel A) (b : RingedTensorModel B)
    (P Q : Complexes A) (hp : Good P) (hq : Good Q) :
    e.left.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      (e.tensorComparison a b).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      B.tensor.map (CategoryTheory.Prod.mkHom (comparison e P) (comparison e Q)) =
    comparison e ((totalTensor A).obj (P, Q)) ≫ DerivedCategory.Q.map (delta e P Q) ≫
      b.representative.hom.app
        (⟨(pull e).obj P, pull_good e hp⟩, ⟨(pull e).obj Q, pull_good e hq⟩) := by
  dsimp only [comparison, delta]
  exact ringedTensorEdgeRepresentativeEquation (A := A) (B := B) e a b P Q hp hq
    (pull_good e hp) (pull_good e hq)

attribute [local irreducible] monoidalCategory
  RingedTensorEdge.tensorComparison ringedTopoiCanonicalDerivedTensorComparison
  derivedPullbackComplexComparison

private theorem comparison_naturality {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P Q : Complexes A} (a : P ⟶ Q) :
    e.left.map (DerivedCategory.Q.map a) ≫ comparison e Q =
      comparison e P ≫ DerivedCategory.Q.map ((pull e).map a) := by
  let eps : DerivedCategory.Q ⋙ e.left ⟶ pull e ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules A)).inv e.left ≫
      Functor.whiskerLeft (HomotopyCategory.quotient (Modules A) (.up ℤ)) e.epsilon ≫
      Functor.whiskerRight (e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft (pull e) (DerivedCategory.quotientCompQhIso (Modules B)).hom
  simpa only [eps, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, comparison,
    derivedPullbackComplexComparison, Category.assoc] using eps.naturality a

private theorem totalTensor_map {A : RingedTensorCorner.{u, w}}
    {P P' Q Q' : Complexes A} (x : P ⟶ P') (y : Q ⟶ Q') :
    (totalTensor A).map (Prod.mkHom x y) =
      HomologicalComplex.mapBifunctorMap x y A.mateTensor (.up ℤ) := by
  simp [totalTensor, Functor.map₂HomologicalComplex, HomologicalComplex.mapBifunctorMap,
    ← HomologicalComplex₂.total.map_comp]

end SheafOfModules.ProjectionCoherence
