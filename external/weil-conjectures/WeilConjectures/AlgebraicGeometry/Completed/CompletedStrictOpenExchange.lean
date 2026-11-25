/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.CategoryTheory.Derived.DerivedPairExchangeNormalization
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
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
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenKFlat
import WeilConjectures.AlgebraicGeometry.Adic.AdicPullbackPresentationModels
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Strict open exchange over completed coefficient rings

Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before Rlim;
Stacks Project, Tags 03DI, 03DJ, 04J0 and 06XN.
(blueprint: def-cbc-completed-strict-open-exchange).

All tower operations precede derived inverse limits. The ordinary inverse exchange
is the already specified adjoint conjugate of the sectionwise cartesian comparison.
Its strict lift and its derived descent retain that normalization. Positive level
n+1 is encoded by n : ℕ. No completeness or quasi-compactness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint limit SheafOfModules.pushforward
  SheafOfModules.extensionByZeroPresheaf PresheafOfModules.sheafification
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory.Q DerivedCategory.Qh

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private def cbcTowerKFlat (T : Scheme.{u})
    (P : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ) : Prop :=
  ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
    (R := pbcAdicCompletion T d)
    ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
      (op n)).mapHomologicalComplex (.up ℤ)).obj P)

private theorem cbcTowerPullback_universal {T S : Scheme.{u}} (g : T ⟶ S) :
    (completedTowerPullback g d).IsLeftDerivedFunctor (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers S (pbcAdicCompletion S d)) (.up ℤ)) := by
  exact adicPresentationTowerUniversal_proof g d

private theorem cbcTowerPullback_computes {T S : Scheme.{u}} (g : T ⟶ S)
    (P : CochainComplex (pbcTowers S (pbcAdicCompletion S d)) ℤ)
    (hP : cbcTowerKFlat d S P) :
    IsIso ((completedTowerPullbackCounit g d).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  unfold completedTowerPullbackCounit completedTowerPullback
  exact (completedTowerPullback_exists g d).choose_spec.choose_spec.2.2 P hP

private theorem functorialFlatResolution
    {B : Type*} [Category B] [Abelian B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    [∀ (j : ℤ), HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) B]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ B] [HasExactColimitsOfShape ℤ B]
    [∀ X : B, PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj X)]
    [∀ X : B, PreservesColimitsOfShape ℤ ((curriedTensor B).obj X)]
    (Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ B))
    [Λ.F.PreservesZeroMorphisms] :
    ∃ (F : CochainComplex B ℤ ⥤ CochainComplex B ℤ) (ε : F ⟶ 𝟭 _),
      (∀ K, (HomologicalComplex.quasiIso B (.up ℤ)).kFlat (F.obj K)) ∧
      (∀ K q, ObjectProperty.flat ((F.obj K).X q)) ∧ ∀ K, QuasiIso (ε.app K) := by
  have hι : (ObjectProperty.flat.ι : _ ⥤ B).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  refine ⟨Λ.resolutionFunctor, Λ.resolutionNatTrans,
    Λ.kFlat_resolutionFunctor_obj hι, ?_, fun _ ↦ inferInstance⟩
  intro K q
  have := CochainComplex.closedUnderColimitsOfShape_flat B ℤ
  let c := Λ.colimitOfShapeResolutionFunctorObj K
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval B (.up ℤ) q) c.isColimit)
    (fun i ↦ hι _ ((c.prop_diag_obj i).1 q))

private def evaluationWhiskerIso
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    (F : B ⥤ C) [F.Additive] (P : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (n : ℕᵒᵖ) :
    (((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapHomologicalComplex (.up ℤ)).obj
        ((((Functor.whiskeringRight ℕᵒᵖ B C).obj F).mapHomologicalComplex (.up ℤ)).obj P) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj
        ((((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ Iso.refl (F.obj ((P.X q).obj n)))
    (by intros; exact (Category.id_comp _).trans (Category.comp_id _).symm)

private theorem cbcTowerKFlat_resolution (T : Scheme.{u})
    (P : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ) :
    ∃ (L : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ) (s : L ⟶ P),
      (cbcTowerKFlat d T L ∧ ∀ (n : ℕ) (q : ℤ), exactFunctor _ _
        (@tensorRight _ _ (SheafOfModules.monoidalCategory (pbcAdicCompletion T d))
          ((L.X q).obj (op n)))) ∧ QuasiIso s := by
  let R := pbcAdicCompletion T d
  let B := pbcModules T R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfi (R := R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  have := SheafOfModules.hasExactColimits_int_kfi R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have (X : B) : PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  classical
  obtain ⟨Λ, hΛ⟩ : ∃ (Λ : Abelian.LeftResolution
      (ObjectProperty.flat.ι : _ ⥤ B)), Λ.F.PreservesZeroMorphisms :=
    ⟨(Classical.arbitrary (Abelian.LeftResolution
      (ObjectProperty.flat.ι : _ ⥤ B))).reduced, inferInstance⟩
  obtain ⟨F, ε, hk, hf, hε⟩ := functorialFlatResolution Λ
  let L := CochainComplex.diagramComplex (P.asFunctor ⋙ F)
  let s : L ⟶ P := CochainComplex.diagramComplexMap (Functor.whiskerLeft P.asFunctor ε)
  refine ⟨L, s, ⟨?_, fun n q ↦ (hf (P.asFunctor.obj (op n)) q).2⟩, ?_⟩
  · intro n
    have hK : CochainComplex.IsKFlatIndependentCoefficients (R := R)
        (F.obj (P.asFunctor.obj (op n))) := by
      intro Z hZ
      let V := tensorRight (F.obj (P.asFunctor.obj (op n)))
      have hz : QuasiIso (0 : (0 : CochainComplex B ℤ) ⟶ Z) := by
        rw [quasiIso_iff]
        intro i
        exact (quasiIsoAt_iff_exactAt _ i
          ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
      have hmap : QuasiIso (V.map (0 : (0 : CochainComplex B ℤ) ⟶ Z)) :=
        (hk (P.asFunctor.obj (op n))).2 _ hz
      have hzero : (V.obj (0 : CochainComplex B ℤ)).Acyclic :=
        HomologicalComplex.acyclic_of_isZero _ (V.map_isZero (isZero_zero _))
      exact fun i ↦ (exactAt_iff_of_quasiIsoAt
        (V.map (0 : (0 : CochainComplex B ℤ) ⟶ Z)) i).1 (hzero i)
    let e : (((CategoryTheory.evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)).obj L ≅
        F.obj (P.asFunctor.obj (op n)) :=
      HomologicalComplex.Hom.isoOfComponents (fun q ↦ Iso.refl _) (by
        intros
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
    exact SheafOfModules.kFlat_iso_independent R e.symm hK
  · rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro n
    exact hε (P.asFunctor.obj n)

/-- Termwise sheafified open extension on actual completed-ring towers.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcStrictOpenModule {U X : Scheme.{u}} (j : U ⟶ X) (hj : IsOpenImmersion j) :
    pbcTowers U (pbcAdicCompletion U d) ⥤ pbcTowers X (pbcAdicCompletion X d) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcOpenShriek d j hj)

/-- Additivity is checked at every tower index.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: extension presheaves, sheafification and slice transport are additive;
apply their sum equation to each component of a tower morphism. -/
@[instance] theorem cbcStrictOpenModule_additive {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) : (cbcStrictOpenModule d j hj).Additive := by
  dsimp only [cbcStrictOpenModule]
  infer_instance

/-- Exactness of extension on towers is levelwise, with no condition on the open.
Source: Stacks 03DJ (blueprint: def-cbc-completed-strict-open-exchange).
Proof: kernels and cokernels of strict diagrams are levelwise. Exactness of
sheafified slice extension therefore preserves both finite limits and colimits. -/
@[instance] theorem cbcStrictOpenModule_limits {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) :
    PreservesFiniteLimits (cbcStrictOpenModule d j hj) := by
  dsimp only [cbcStrictOpenModule]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Finite colimits are preserved at each tower index.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: the slice extension is left adjoint to restriction, hence preserves finite
colimits. Colimits of strict diagrams are computed at each index. -/
@[instance] theorem cbcStrictOpenModule_colimits {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) :
    PreservesFiniteColimits (cbcStrictOpenModule d j hj) := by
  dsimp only [cbcStrictOpenModule]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Exact open extension on the derived category of strict towers.
Source: Stacks 03DJ (blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcStrictOpen {U X : Scheme.{u}} (j : U ⟶ X) (hj : IsOpenImmersion j) :=
  (cbcStrictOpenModule d j hj).mapDerivedCategory

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

/-- Naturality of the fixed inverse exchange along a strict tower transition.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: apply naturality of cbcUnderivedInverseExchange to the specified tower map. -/
theorem cbcStrictInverseLevel_naturality
    (M : pbcTowers U (pbcAdicCompletion U d)) (a b : ℕᵒᵖ) (f : a ⟶ b) :
    ((completedTowerModulePullback gU d ⋙
        cbcStrictOpenModule d j' sq.isOpenImmersion').obj M).map f ≫
      (cbcUnderivedInverseExchange d sq).app (M.obj b) =
    (cbcUnderivedInverseExchange d sq).app (M.obj a) ≫
      ((cbcStrictOpenModule d j sq.isOpenImmersion ⋙
        completedTowerModulePullback g d).obj M).map f := by
  exact (cbcUnderivedInverseExchange d sq).naturality (M.map f)

/-- The inverse exchange as an actual map of strict towers.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcStrictInverseComponent (M : pbcTowers U (pbcAdicCompletion U d)) :
    (completedTowerModulePullback gU d ⋙
      cbcStrictOpenModule d j' sq.isOpenImmersion').obj M ⟶
    (cbcStrictOpenModule d j sq.isOpenImmersion ⋙
      completedTowerModulePullback g d).obj M where
  app n := (cbcUnderivedInverseExchange d sq).app (M.obj n)
  naturality a b f := cbcStrictInverseLevel_naturality d sq M a b f

/-- Naturality in the original strict tower.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: at every index apply ordinary inverse-exchange naturality to that component
of the tower morphism. Extensionality of natural transformations gives the result. -/
theorem cbcStrictInverseComponent_naturality
    (M N : pbcTowers U (pbcAdicCompletion U d)) (f : M ⟶ N) :
    (completedTowerModulePullback gU d ⋙
      cbcStrictOpenModule d j' sq.isOpenImmersion').map f ≫
        cbcStrictInverseComponent d sq N =
    cbcStrictInverseComponent d sq M ≫
      (cbcStrictOpenModule d j sq.isOpenImmersion ⋙
        completedTowerModulePullback g d).map f := by
  apply NatTrans.ext
  funext n
  exact (cbcUnderivedInverseExchange d sq).naturality (f.app n)

/-- Simultaneous inverse diagram map. Its component at every index is the fixed
ordinary inverse exchange, the conjugate of restriction along the cartesian map.
The forward diagram map is its inverse, already before derived localization.
Source: Stacks 03DI, 04J0 (blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcStrictInverseModule :
    completedTowerModulePullback gU d ⋙ cbcStrictOpenModule d j' sq.isOpenImmersion' ⟶
      cbcStrictOpenModule d j sq.isOpenImmersion ⋙ completedTowerModulePullback g d where
  app M := cbcStrictInverseComponent d sq M
  naturality M N f := cbcStrictInverseComponent_naturality d sq M N f

/-- The simultaneous strict maps are inverse, component by component.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: the inverse at each index is the forward ordinary exchange. Naturality
makes both maps strict; their composites are identities at each index. -/
@[instance] theorem cbcStrictInverseModule_isIso : IsIso (cbcStrictInverseModule d sq) := by
  have (M : pbcTowers U (pbcAdicCompletion U d)) :
      IsIso ((cbcStrictInverseModule d sq).app M) := by
    have (n : ℕᵒᵖ) : IsIso (((cbcStrictInverseModule d sq).app M).app n) := by
      change IsIso ((cbcUnderivedInverseExchange d sq).app (M.obj n))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- The strict representative equation, using the actual universal pullback counits.
It specifies the inverse map, so also specifies its forward inverse uniquely.
Source: Stacks 06XN (blueprint: def-cbc-completed-strict-open-exchange). -/
def CbcStrictExchangeNormalization
    (b : cbcStrictOpen d j sq.isOpenImmersion ⋙ completedTowerPullback g d ≅
      completedTowerPullback gU d ⋙ cbcStrictOpen d j' sq.isOpenImmersion') : Prop :=
  DerivedPairExchangeNormalization
    (completedTowerModulePullback gU d) (completedTowerModulePullback g d)
    (cbcStrictOpenModule d j sq.isOpenImmersion)
    (cbcStrictOpenModule d j' sq.isOpenImmersion')
    (completedTowerPullback gU d) (completedTowerPullback g d)
    (completedTowerPullbackCounit gU d) (completedTowerPullbackCounit g d)
    (cbcStrictInverseModule d sq)
    (fun P ↦ ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion U d)
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules U (pbcAdicCompletion U d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P)) b

private theorem modelPullPair_existsUnique
    {B C T V : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [Category T] [Abelian T] [Category V] [Abelian V]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory T] [HasDerivedCategory V]
    (F : B ⥤ T) [F.Additive] (G : C ⥤ V) [G.Additive]
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (H : T ⥤ V) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {M : CochainComplex B ℤ → Prop} {N : CochainComplex C ℤ → Prop}
    (LF : DerivedCategory B ⥤ DerivedCategory T)
    (LG : DerivedCategory C ⥤ DerivedCategory V)
    (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor εF (HomotopyCategory.quasiIso B (.up ℤ)))
    (hLG : LG.IsLeftDerivedFunctor εG (HomotopyCategory.quasiIso C (.up ℤ)))
    (hF : ∀ K : CochainComplex B ℤ, M K →
      IsIso (εF.app ((HomotopyCategory.quotient B (.up ℤ)).obj K)))
    (hG : ∀ K : CochainComplex C ℤ, N K →
      IsIso (εG.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)))
    (e : F ⋙ H ⟶ P ⋙ G) [IsIso e]
    (M₀ : CochainComplex B ℤ → Prop) (h₀ : ∀ K, M₀ K → M K)
    (res : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      M₀ L ∧ QuasiIso s)
    (hmap : ∀ K, M₀ K → N ((P.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃! b : P.mapDerivedCategory ⋙ LG ≅ LF ⋙ H.mapDerivedCategory,
      DerivedPairExchangeNormalization F G P H LF LG εF εG e M b := by
  let DF : DerivedReductionModelData F M := ⟨LF, εF, hLF, hF⟩
  let DG : DerivedReductionModelData G N := ⟨LG, εG, hLG, hG⟩
  obtain ⟨η, hη, hu⟩ :=
    OrderedExchange.modelPull_existsUnique F G P H DF DG (asIso e) M₀ h₀ res hmap
  refine ⟨η.symm, ?_, ?_⟩
  · intro K hK
    exact heq_of_eq (hη K hK)
  · intro b hb
    have h := hu b.symm (fun K hK ↦ eq_of_heq (hb K hK))
    exact congrArg Iso.symm h

attribute [local irreducible] cbcStrictOpenModule completedTowerModulePullback
  completedTowerPullbackCounit cbcStrictInverseModule cbcUnderivedInverseExchange

/-- The normalized strict exchange exists uniquely.
Source: Stacks 03DI, 03DJ, 04J0, 06XN and the blueprint finite-exchange refinement
(blueprint: def-cbc-completed-strict-open-exchange).
Proof: (1) localization identifies both restricted completed rings, projection by
projection. (2) Compose open-extension and module-pullback adjunctions.
(3) Restriction along the cartesian comparison gives the right-adjoint isomorphism.
(4) Conjugation gives the already specified ordinary inverse exchange and its inverse.
(5) Apply these maps simultaneously at every index and cochain degree; naturality
commutes with all transitions and differentials. (6) Take a strict objectwise
K-flat flat-term replacement. Open extension preserves this resolving class by
the slice tensor projection formula. The two maps thus descend through the
universal left-derived counits. Their strict inverse identities descend as well.
The displayed representative equation and resolving-class universality give uniqueness. -/
theorem cbcStrictExchange_existsUnique :
    ∃! b : cbcStrictOpen d j sq.isOpenImmersion ⋙ completedTowerPullback g d ≅
        completedTowerPullback gU d ⋙ cbcStrictOpen d j' sq.isOpenImmersion',
      CbcStrictExchangeNormalization d sq b := by
  let M₀ : CochainComplex (pbcTowers U (pbcAdicCompletion U d)) ℤ → Prop :=
    fun P ↦ cbcTowerKFlat d U P ∧ ∀ (n : ℕ) (q : ℤ), exactFunctor _ _
      (@tensorRight _ _ (SheafOfModules.monoidalCategory (pbcAdicCompletion U d))
        ((P.X q).obj (op n)))
  have hmap (P) (hP : M₀ P) : cbcTowerKFlat d X
      (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj
        P) := by
    unfold cbcTowerKFlat
    intro n
    let Q := (((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules U (pbcAdicCompletion U d))).obj (op n)).mapHomologicalComplex
        (.up ℤ)).obj P
    have hQ := cbcOpenShriek_kFlat_of_flatTerms d j sq.isOpenImmersion
      Q (hP.1 n) (hP.2 n)
    let e := evaluationWhiskerIso (cbcOpenShriek d j sq.isOpenImmersion) P (op n)
    simpa only [cbcStrictOpenModule] using
      (SheafOfModules.kFlat_iso_independent (pbcAdicCompletion X d) e.symm hQ)
  exact modelPullPair_existsUnique
    (B := pbcTowers U (pbcAdicCompletion U d))
    (C := pbcTowers X (pbcAdicCompletion X d))
    (T := pbcTowers U' (pbcAdicCompletion U' d))
    (V := pbcTowers X' (pbcAdicCompletion X' d))
    (M := cbcTowerKFlat d U) (N := cbcTowerKFlat d X)
    (completedTowerModulePullback gU d) (completedTowerModulePullback g d)
    (cbcStrictOpenModule d j sq.isOpenImmersion)
    (cbcStrictOpenModule d j' sq.isOpenImmersion')
    (completedTowerPullback gU d) (completedTowerPullback g d)
    (completedTowerPullbackCounit gU d) (completedTowerPullbackCounit g d)
    (cbcTowerPullback_universal d gU) (cbcTowerPullback_universal d g)
    (cbcTowerPullback_computes d gU) (cbcTowerPullback_computes d g)
    (cbcStrictInverseModule d sq) M₀ (fun _ h ↦ h.1)
    (cbcTowerKFlat_resolution d U) hmap

/-- The canonical strict exchange, selected by its unique representative equation.
Source: Stacks 03DI, 06XN (blueprint: def-cbc-completed-strict-open-exchange). -/
@[irreducible] def cbcStrictExchange := (cbcStrictExchange_existsUnique d sq).exists.choose

/-- The asserted natural isomorphism on reductions of arbitrary completed-ring objects.
Source: blueprint finite exchange before Rlim
(blueprint: def-cbc-completed-strict-open-exchange). -/
def cbcReductionStrictExchange :
    completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
        completedTowerPullback g d ≅
      completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
        cbcStrictOpen d j' sq.isOpenImmersion' :=
  Functor.isoWhiskerLeft (completedReductionTower U d) (cbcStrictExchange d sq)

end AlgebraicGeometry.Scheme
