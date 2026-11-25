/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain
import WeilConjectures.CategoryTheory.RingedKoszulDualizable
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-! # KoszulScalarHomDiagram for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-hom-diagram).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

private def homRestriction (φ : R ⟶ B) (N : ringedSiteComplex B) :
    ((extension φ).mapHomologicalComplex (.up ℤ)).op ⋙
        (homComplexFunctor (R := B)).flip.obj N ⋙ restrictComplex φ ≅
      (homComplexFunctor (R := R)).flip.obj ((restrictComplex φ).obj N) := by
  refine NatIso.ofComponents (fun P ↦
    (SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta P.unop N) ?_
  intro P Q f
  simpa only [SheafOfModules.StrictScalarHom.homMap, Functor.map_id,
    HomologicalComplex.id_f, Category.comp_id] using!
    (SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta_natural
      P.unop Q.unop N N f.unop (𝟙 N)

private def homDiagramComparison (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a)) (N : ringedSiteComplex B) :
    (ringedKoszulDiagram B r (imageSections φ a)).op ⋙
        (homComplexFunctor (R := B)).flip.obj N ⋙ restrictComplex φ ≅
      (ringedKoszulDiagram R r a).op ⋙
        (homComplexFunctor (R := R)).flip.obj ((restrictComplex φ).obj N) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (NatIso.op e) ((homComplexFunctor (R := B)).flip.obj N))
      (restrictComplex φ) ≪≫
    Functor.isoWhiskerLeft (ringedKoszulDiagram R r a).op (homRestriction φ N)

private def koszulEvaluation (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O) :
    (ringedKoszulTensorTower O r a).obj N ≅
      (ringedKoszulDiagram O r a).op ⋙ (homComplexFunctor (R := O)).flip.obj N := by
  have (m : ℕᵒᵖ) :
      IsIso (ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r a).obj m.unop) N) :=
    ringedComplexTensorEvaluation_isIso O _ N (ringedKoszulStage_dualizable O r a m.unop)
  exact NatIso.ofComponents
    (fun m ↦ asIso
      (ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r a).obj m.unop) N))
    (fun f ↦ ringedComplexTensorEvaluation_source O
      ((ringedKoszulDiagram O r a).map f.unop) N)

/-- Comparison through the finite Koszul Hom diagram.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: The theta isomorphisms of the normalized scalar-Hom adjunction form a natural
transformation in the source by theta_natural. Precompose the B Hom diagram by the given positive
comparison and compose with theta to obtain homDiagramComparison.
Proof step 2: Every finite positive Koszul stage is dualizable, so canonical tensor-Hom
evaluation is an isomorphism. Its source naturality makes these stage isomorphisms natural in the
inverse diagram. Whisker B evaluation with restriction, compose with homDiagramComparison and
inverse R evaluation.
(blueprint: lem-f5-koszul-scalar-hom-diagram). -/
private def tensorDiagramComparison (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a)) (N : ringedSiteComplex B) :
    (ringedKoszulTensorTower B r (imageSections φ a)).obj N ⋙ restrictComplex φ ≅
      (ringedKoszulTensorTower R r a).obj ((restrictComplex φ).obj N) :=
  Functor.isoWhiskerRight (koszulEvaluation B r (imageSections φ a) N)
      (restrictComplex φ) ≪≫
    homDiagramComparison φ r a e N ≪≫
    (koszulEvaluation R r a ((restrictComplex φ).obj N)).symm

/-- Transport a commuting square through a functor and a further commuting square.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-hom-diagram). -/
theorem naturalityCompositionCore
    {D : Type*} [Category D] {D' : Type*} [Category D'] (F : D ⥤ D')
    {X Y X' Y' : D} {N M : D'}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (t : F.obj X' ⟶ N) (u : F.obj Y' ⟶ M) (k : N ⟶ M)
    (hc : f ≫ b = a ≫ g) (ht : F.map g ≫ u = t ≫ k) :
    F.map f ≫ (F.map b ≫ u) = (F.map a ≫ t) ≫ k := by
  calc
    _ = F.map (f ≫ b) ≫ u := by rw [F.map_comp, Category.assoc]
    _ = F.map (a ≫ g) ≫ u := congrArg (fun z ↦ F.map z ≫ u) hc
    _ = _ := by rw [F.map_comp, Category.assoc, ht, Category.assoc]

end CategoryTheory.FlatScalarKoszul
