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
/-!
# Normalized models for adic pullback presentations

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md; Stacks Tags 05S7 and 03DI.
(blueprint: lem-cbc-adic-pullback-presentation-models).

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

-- A normalized comparison on resolving objects descends through fully faithful restriction.
private theorem normalizedComparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : C ⥤ D) (P : ObjectProperty C)
    (ff : ((whiskeringLeft P.FullSubcategory D E).obj (P.ι ⋙ Q)).FullyFaithful)
    (F G : D ⥤ E) (H : C ⥤ E) (α : Q ⋙ F ⟶ H) (β : Q ⋙ G ⟶ H)
    (ha : ∀ X, P X → IsIso (α.app X)) (hb : ∀ X, P X → IsIso (β.app X)) :
    ∃! e : F ≅ G, ∀ X, P X → α.app X = e.hom.app (Q.obj X) ≫ β.app X := by
  let a : P.ι ⋙ Q ⋙ F ≅ P.ι ⋙ H :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (α.app X.obj) (ha X.obj X.property))
      (fun f ↦ α.naturality f.hom)
  let b : P.ι ⋙ Q ⋙ G ≅ P.ι ⋙ H :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (β.app X.obj) (hb X.obj X.property))
      (fun f ↦ β.naturality f.hom)
  let e := ff.preimageIso (a ≪≫ b.symm)
  have he (X : P.FullSubcategory) :
      e.hom.app (Q.obj X.obj) = (a ≪≫ b.symm).hom.app X :=
    congrArg (fun z ↦ z.app X) (ff.map_preimage (a ≪≫ b.symm).hom)
  have hs : ∀ X, P X → α.app X = e.hom.app (Q.obj X) ≫ β.app X := by
    intro X hX
    rw [he ⟨X, hX⟩]
    have := hb X hX
    simp [a, b]
  refine ⟨e, hs, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ff.map_injective
  ext X
  change e'.hom.app (Q.obj X.obj) = e.hom.app (Q.obj X.obj)
  have := hb X.obj X.property
  exact (cancel_mono (β.app X.obj)).1
    ((he' X.obj X.property).symm.trans (hs X.obj X.property))

private def complexCounit
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm L).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) ε ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
      DerivedCategory.Qh).hom ≫
    (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D)).hom

private def EvaluationNormalization
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive]
    (FT : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ D)) [FT.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (T : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory (ℕᵒᵖ ⥤ D))
    (τ : DerivedCategory.Qh ⋙ T ⟶
      FT.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (n : ℕ)
    (e : FT.mapHomologicalComplex (.up ℤ) ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapHomologicalComplex (.up ℤ) ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
        F.mapHomologicalComplex (.up ℤ))
    (good : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ C) ℤ))
    (v : T ⋙ ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapDerivedCategory ⋙ L) : Prop :=
  ∀ P, good P →
    (((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategory).map
        (Functor.leftDerivedCounitOnComplex
          FT T τ P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategoryFactors.hom.app
        ((FT.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (e.hom.app P) =
    v.hom.app (DerivedCategory.Q.obj P) ≫
      L.map (((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapDerivedCategoryFactors.hom.app
        P) ≫
      Functor.leftDerivedCounitOnComplex F L ε
        ((((CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)).mapHomologicalComplex (.up ℤ)).obj P)

namespace CochainComplex

-- Resolve the entire tower functorially, so its transition maps remain strict.
end CochainComplex

namespace AlgebraicGeometry.Scheme

private theorem canonicalTowerPair {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    IsCompletedTowerPullbackPair g d
      (completedTowerPullback g d) (completedTowerPullbackCounit g d) := by
  unfold completedTowerPullback completedTowerPullbackCounit
  exact (completedTowerPullback_exists g d).choose_spec.choose_spec

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

private theorem constantDirect_naturality
    {B C : CommRingCat.{u + 1}} (φ : B ⟶ C) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map φ ≫
        proEtaleConstantDirectImageMap g CommRingCat.{u + 1} C =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} B ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map φ) := by
  apply ((sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv _ _).injective
  change (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map φ) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact congr_app
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map φ))
      ((proEtaleBaseChange g).op.obj V)

/-- Proof that the published strict-tower pair is a universal left-derived pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-models).
Proof: completedTowerPullback_exists constructs this pair by strict diagram K-flat
replacements. Its first property is precisely the universal derived property. -/
theorem adicPresentationTowerUniversal_proof :
    (completedTowerPullback g d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  exact (canonicalTowerPair g d).1

section Ordinary
variable (L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]

end Ordinary

section Tower
variable (L : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

end Tower

section NormalizedPair
variable
  (L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [hL : L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ : DerivedCategory.Qh ⋙ T ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [hT : T.IsLeftDerivedFunctor τ
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

end NormalizedPair

end AlgebraicGeometry.Scheme
