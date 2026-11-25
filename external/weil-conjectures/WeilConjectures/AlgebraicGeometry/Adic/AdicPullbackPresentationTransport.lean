/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.CategoryTheory.Adjunction.Mates

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientTransitionCompatibility
import all WeilConjectures.Algebra.Homology.ProperBaseChange.DiagramKFlatReplacements
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import all WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
public import WeilConjectures.AlgebraicGeometry.Adic.AdicPullbackPresentationModels
import all WeilConjectures.AlgebraicGeometry.Adic.AdicPullbackPresentationModels

set_option linter.privateModule false
/-!
# Counit-normalized transport of adic pullback presentations

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md; Stacks Tags 05S7 and 03DI.
(blueprint: lem-cbc-adic-pullback-presentation-transport).

The coefficient uniqueness statement first identifies both presentations with the published
coefficient map. The subsequent statements use these identifications to write both universal
pairs over the same ordinary functor. No invertibility of the completed coefficient map is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

section Pairs
variable
  (L₁ L₂ : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L₁.IsLeftDerivedFunctor ε₁
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [L₂.IsLeftDerivedFunctor ε₂
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T₁ T₂ : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ₁ : DerivedCategory.Qh ⋙ T₁ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (τ₂ : DerivedCategory.Qh ⋙ T₂ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [T₁.IsLeftDerivedFunctor τ₁
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [T₂.IsLeftDerivedFunctor τ₂
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

end Pairs

section CompletionTransport
end CompletionTransport

section TransportSquares
variable
  (L₁ L₂ : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L₁.IsLeftDerivedFunctor ε₁
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [L₂.IsLeftDerivedFunctor ε₂
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T₁ T₂ : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ₁ : DerivedCategory.Qh ⋙ T₁ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (τ₂ : DerivedCategory.Qh ⋙ T₂ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [T₁.IsLeftDerivedFunctor τ₁
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [T₂.IsLeftDerivedFunctor τ₂
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (e : L₁ ≅ L₂) (et : T₁ ≅ T₂)
  (hε : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ ε₂ = ε₁)
  (hτ : Functor.whiskerLeft DerivedCategory.Qh et.hom ≫ τ₂ = τ₁)

end TransportSquares

-- Restriction is inverse image along the corresponding site object.
@[irreducible] private noncomputable def finiteUnderlying {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModulePullback g R S c ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ proEtaleSheafInverseImage g AddCommGrpCat.{u + 1} := by
  let hx := SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let theta := hx.choose
  have hn := hx.choose_spec.2.2
  let b : proEtaleRingModulePullback g R S c ⋙ SheafOfModules.toSheaf _ ≅
      proEtaleModuleInverseImage g R ⋙ SheafOfModules.toSheaf _ :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.toSheaf _).mapIso (theta ((proEtaleModuleInverseImage g R).obj M)) ≪≫
        ObjectProperty.isoMk _ (Iso.refl _)) (by
          intro M N f
          have h := hn _ _ ((proEtaleModuleInverseImage g R).map f)
          have hleft : (proEtaleRingModulePullback g R S c).map f =
              SheafOfModules.changeOfRingsHomOfUniverses c.hom
                ((proEtaleModuleInverseImage g R).obj M)
                ((proEtaleModuleInverseImage g R).map f) := by rfl
          have hright : ((SheafOfModules.toSheaf _).map
              ((SheafOfModules.restrictScalars
                ((sheafCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).map
                  ((proEtaleModuleInverseImage g R).map f))).hom =
              ((SheafOfModules.toSheaf _).map
                ((proEtaleModuleInverseImage g R).map f)).hom := by rfl
          apply ObjectProperty.hom_ext
          simpa only [Functor.comp_map, hleft, hright, Functor.map_comp,
            ObjectProperty.FullSubcategory.comp_hom,
            Iso.trans_hom, Functor.mapIso_hom, ObjectProperty.isoMk_hom,
            ObjectProperty.homMk_hom, Iso.refl_hom, Category.comp_id,
            Category.id_comp] using
              congrArg (fun f ↦ f.hom) (congrArg (SheafOfModules.toSheaf _).map h))
  exact b ≪≫ (proEtale_moduleInverseImage_comparison g R).1.some

section OpenMateTransport
variable (U : Y.ProEt) [hU : IsOpenImmersion U.hom] (n : ℕ)

end OpenMateTransport

end AlgebraicGeometry.Scheme
