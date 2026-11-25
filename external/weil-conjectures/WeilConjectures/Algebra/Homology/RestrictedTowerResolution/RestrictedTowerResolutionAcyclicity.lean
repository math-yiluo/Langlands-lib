/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Sites.KInjectiveComparisonPrinciple
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
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
import WeilConjectures.CategoryTheory.GeometricRingTransport
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Restricted varying-ring resolutions and their inverse-limit projections

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0D6E
(blueprint: lem-coef-restricted-tower-resolution-acyclicity).

The ordinary functors below are constructed on sections. The direct image of the
ringed sequence projection is the compatible-family limit after scalar restriction.
The index `n : ℕ` denotes positive level `n+1`. All complexes are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w d s t
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.RestrictedTowerResolution

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
  (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)

/-- The existing category of modules over the base ring sheaf.
Source: Stacks 03CZ (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
abbrev Modules := ringedSiteModules.{w}
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)

/-- Actual restriction of scalars at level `n+1`.
Source: Stacks 03CZ (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
abbrev restriction (n : ℕ) : systemLevel B n ⥤ Modules A :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (α.app (op n)))

/-- The canonical coefficient-composition identification, with identity section maps.
Source: Stacks 03CZ (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
def restrictionComposition {m n : ℕ} (h : m ≤ n) :
    systemRestriction B h ⋙ restriction A B α n ≅ restriction A B α m :=
  systemScalarRestrictionComposition _ _ _ (by
    simpa using α.naturality (homOfLE h).op)

/-- Restrict the actual system, retaining its given horizontal maps.
Source: Stacks 0940 (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
def tower (N : StrictRingSystem B) : ℕᵒᵖ ⥤ Modules A where
  obj n := (restriction A B α n.unop).obj (N.level n.unop)
  map {n m} h := (restriction A B α n.unop).map (N.transition (leOfHom h.unop)) ≫
    (restrictionComposition A B α (leOfHom h.unop)).hom.app _
  map_id n := by
    ext U x
    exact N.identity n.unop U x
  map_comp {n m l} h k := by
    ext U x
    exact N.compose (leOfHom k.unop) (leOfHom h.unop) U x

/-- The actual scalar-restriction functor U0, on both objects and morphisms.
Source: Stacks 03CZ and 0940
(blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
def restrictionFunctor : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ Modules A) where
  obj := tower A B α
  map {N N'} f :=
    { app := fun n ↦ (restriction A B α n.unop).map (f.app n.unop)
      naturality := by
        intro n m h
        ext U x
        exact (congrArg (fun t ↦ t.val.app U x) (f.comm (leOfHom h.unop))).symm }
  map_id N := by ext n U x; rfl
  map_comp f g := by ext n U x; rfl

/-- U0 is additive because its component maps are unchanged additive maps.
Source: Stacks 03CZ (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
instance restrictionFunctorAdditive : (restrictionFunctor A B α).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext n
    change ((systemEvaluation B n.unop) ⋙ restriction A B α n.unop).map (f + g) = _
    exact Functor.map_add _

/-- The ordinary sequence-projection direct image p_*: sections are the compatible
families of underlying sections with the A-action induced by α. This is g_*r_*, with
r_* the actual scalar restriction above and g_* the actual tower limit.
Source: Stacks 0940 (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
abbrev directImage : StrictRingSystem B ⥤ Modules A := restrictionFunctor A B α ⋙ lim

/-- Additivity of inverse limit, obtained from preservation of finite products.
Source: Stacks 0940 (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
instance limitAdditive : (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).Additive := by
  have : HasLimitsOfShape (Discrete WalkingPair) (Modules A) :=
    SheafOfModules.hasLimitsOfShape _ _
  have : HasLimitsOfShape (Discrete WalkingPair) (ℕᵒᵖ ⥤ Modules A) :=
    functorCategoryHasLimitsOfShape
  exact Functor.additive_of_preserves_binary_products _

/-- The existing degreewise inverse-limit functor on complexes.
Source: Stacks 0940 (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
abbrev limitComplex := (lim : (ℕᵒᵖ ⥤ Modules A) ⥤ Modules A).mapHomologicalComplex (.up ℤ)

/-- Restriction applied in every degree of a complex.
Source: Stacks 03CZ (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
abbrev restrictionComplex := (restrictionFunctor A B α).mapHomologicalComplex (.up ℤ)

/-- The actual degreewise inverse-limit projection.
Source: Stacks 0940 (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
def projection (T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ) (n : ℕ) :
    (limitComplex A).obj T ⟶ T.asFunctor.obj (op n) :=
  (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app T

/-- The map of complexes obtained by exact evaluation of a tower at level `n+1`.
Source: Stacks 0940 (blueprint: lem-coef-restricted-tower-resolution-acyclicity). -/
def componentMap {S T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ} (f : S ⟶ T) (n : ℕ) :
    S.asFunctor.obj (op n) ⟶ T.asFunctor.obj (op n) :=
  (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)

omit [EssentiallySmall.{w} C] in
/-- Scalar restriction r_*=U0 is exact, with no flatness requirement.
Source: Stacks 03CZ and 0940
(blueprint: lem-coef-restricted-tower-resolution-acyclicity).
Proof: step 1 of the node. Restriction leaves underlying abelian sheaves and their
maps unchanged. The componentwise kernels and sheafified cokernels are therefore
unchanged; componentwise exactness of strict systems gives both preservation claims. -/
theorem restrictionFunctor_exact :
    PreservesFiniteLimits (restrictionFunctor A B α) ∧
      PreservesFiniteColimits (restrictionFunctor A B α) := by
  constructor
  · apply preservesFiniteLimits_of_evaluation
    intro n
    change PreservesFiniteLimits (systemEvaluation B n.unop ⋙ restriction A B α n.unop)
    exact comp_preservesFiniteLimits _ _
  · apply preservesFiniteColimits_of_evaluation
    intro n
    change PreservesFiniteColimits (systemEvaluation B n.unop ⋙ restriction A B α n.unop)
    exact comp_preservesFiniteColimits _ _

private abbrev scalar (n : ℕ) := SequenceProjection.scalar A B α n

private def extensionTowerObj (P : ℕᵒᵖ ⥤ Modules A) : StrictRingSystem B where
  level n := (scalar A B α n).model.E.obj (P.obj (op n))
  transition {m n} h := (scalar A B α n).model.E.map (P.map (homOfLE h).op) ≫
    SequenceProjection.transition A B α (P.obj (op m)) h
  identity n U x := by
    have he := (SequenceProjection.extensionObj A B α (P.obj (op n))).identity n U x
    change (SequenceProjection.transition A B α (P.obj (op n)) (Nat.le_refl n)).val.app U
      (((scalar A B α n).model.E.map (P.map (𝟙 (op n)))).val.app U x) = x
    rw [P.map_id, (scalar A B α n).model.E.map_id]
    exact he
  compose {l m n} h k U x := by
    let e := systemScalarRestrictionComposition (B.map (homOfLE k).op)
      (B.map (homOfLE h).op) (B.map (homOfLE (h.trans k)).op)
      (by rw [← B.map_comp]; rfl)
    have he :
        (scalar A B α n).model.E.map (P.map (homOfLE (h.trans k)).op) ≫
            SequenceProjection.transition A B α (P.obj (op l)) (h.trans k) =
          ((scalar A B α n).model.E.map (P.map (homOfLE k).op) ≫
            SequenceProjection.transition A B α (P.obj (op m)) k) ≫
          (systemRestriction B k).map
            ((scalar A B α m).model.E.map (P.map (homOfLE h).op) ≫
              SequenceProjection.transition A B α (P.obj (op l)) h) ≫ e.hom.app _ := by
      apply systemScalarModel_hom_ext (scalar A B α n)
      intro V y
      change (SequenceProjection.transition A B α (P.obj (op l)) (h.trans k)).val.app V
        (((scalar A B α n).model.E.map (P.map (homOfLE (h.trans k)).op)).val.app V _) =
        (SequenceProjection.transition A B α (P.obj (op l)) h).val.app V
        (((scalar A B α m).model.E.map (P.map (homOfLE h).op)).val.app V
          ((SequenceProjection.transition A B α (P.obj (op m)) k).val.app V
            (((scalar A B α n).model.E.map (P.map (homOfLE k).op)).val.app V _)))
      simp only [systemScalarModel_map_tmul, SequenceProjection.transition_tmul, map_one]
      congr 1
      exact congrArg (fun f ↦ f.val.app V y) (P.map_comp (homOfLE k).op (homOfLE h).op)
    exact congrArg (fun f ↦ f.val.app U x) he

private def extensionTowerMap {P Q : ℕᵒᵖ ⥤ Modules A} (f : P ⟶ Q) :
    extensionTowerObj A B α P ⟶ extensionTowerObj A B α Q where
  app n := (scalar A B α n).model.E.map (f.app (op n))
  comm {m n} h := by
    apply systemScalarModel_hom_ext (scalar A B α n)
    intro U x
    change _ = ((scalar A B α m).model.E.map (f.app (op m))).val.app U
      ((SequenceProjection.transition A B α (P.obj (op m)) h).val.app U
        (((scalar A B α n).model.E.map (P.map (homOfLE h).op)).val.app U _))
    change (SequenceProjection.transition A B α (Q.obj (op m)) h).val.app U
      (((scalar A B α n).model.E.map (Q.map (homOfLE h).op)).val.app U
        (((scalar A B α n).model.E.map (f.app (op n))).val.app U _)) = _
    rw [systemScalarModel_map_tmul, systemScalarModel_map_tmul,
      SequenceProjection.transition_tmul, systemScalarModel_map_tmul,
      SequenceProjection.transition_tmul, systemScalarModel_map_tmul]
    congr 1
    exact congrArg (fun g ↦ g.val.app U x) (f.naturality (homOfLE h).op).symm

private def extensionTower : (ℕᵒᵖ ⥤ Modules A) ⥤ StrictRingSystem B where
  obj := extensionTowerObj A B α
  map := extensionTowerMap A B α
  map_id _P := strictRingSystem_hom_ext B _ _ (fun n ↦
    (scalar A B α n).model.E.map_id _)
  map_comp _f _g := strictRingSystem_hom_ext B _ _ (fun n ↦
    (scalar A B α n).model.E.map_comp _ _)

private instance extensionTower_additive : (extensionTower A B α).Additive where
  map_add := by
    intro P Q f g
    apply strictRingSystem_hom_ext B
    intro n
    change (scalar A B α n).model.E.map (f.app (op n) + g.app (op n)) = _
    rw [(scalar A B α n).model.E.map_add]
    exact ((systemEvaluation B n).map_add (f := (extensionTower A B α).map f)
      (g := (extensionTower A B α).map g)).symm

private def extensionTowerTranspose {P : ℕᵒᵖ ⥤ Modules A} {N : StrictRingSystem B}
    (f : (extensionTower A B α).obj P ⟶ N) : P ⟶ (restrictionFunctor A B α).obj N where
  app n := (scalar A B α n.unop).ordinaryAdj.homEquiv _ _ (f.app n.unop)
  naturality {n m} h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    have hf := congrArg (fun g ↦
      (((restriction A B α n.unop).map g ≫
        (restrictionComposition A B α (leOfHom h.unop)).hom.app _).val.app U)
        (systemModelTmul (scalar A B α n.unop).model (P.obj n) U 1 x))
      (f.comm (leOfHom h.unop))
    change (N.transition _).val.app U
      ((f.app n.unop).val.app U
        (systemModelTmul (scalar A B α n.unop).model (P.obj n) U 1 x)) =
      (f.app m.unop).val.app U
        ((SequenceProjection.transition A B α (P.obj m)
          (leOfHom h.unop)).val.app U
          (((scalar A B α n.unop).model.E.map (P.map h)).val.app U
            (systemModelTmul (scalar A B α n.unop).model (P.obj n) U 1 x))) at hf
    rw [systemScalarModel_map_tmul, SequenceProjection.transition_tmul,
      map_one] at hf
    erw [systemScalarModel_transpose_tmul (scalar A B α n.unop) _ _ (f.app n.unop),
      systemScalarModel_transpose_tmul (scalar A B α m.unop) _ _ (f.app m.unop)] at hf
    change (((scalar A B α m.unop).ordinaryAdj.homEquiv _ _ (f.app m.unop)).val.app U)
        ((P.map h).val.app U x) =
      (N.transition (leOfHom h.unop)).val.app U
        ((((scalar A B α n.unop).ordinaryAdj.homEquiv _ _ (f.app n.unop)).val.app U) x)
    simp only [one_smul] at hf
    dsimp only [systemRestriction, restrictScalars, PresheafOfModules.restrictScalars,
      PresheafOfModules.restrictScalarsObj, ModuleCat.restrictScalars,
      ModuleCat.RestrictScalars.obj'] at hf ⊢
    exact hf.symm

private def extensionTowerUntranspose {P : ℕᵒᵖ ⥤ Modules A} {N : StrictRingSystem B}
    (f : P ⟶ (restrictionFunctor A B α).obj N) : (extensionTower A B α).obj P ⟶ N where
  app n := ((scalar A B α n).ordinaryAdj.homEquiv _ _).symm (f.app (op n))
  comm {m n} h := by
    apply systemScalarModel_hom_ext (scalar A B α n)
    intro U x
    have hf := congrArg (fun g ↦ g.val.app U x) (f.naturality (homOfLE h).op)
    change (N.transition h).val.app U
      ((((scalar A B α n).ordinaryAdj.homEquiv _ _).symm (f.app (op n))).val.app U _) =
      ((((scalar A B α m).ordinaryAdj.homEquiv _ _).symm (f.app (op m))).val.app U
        ((SequenceProjection.transition A B α (P.obj (op m)) h).val.app U
          (((scalar A B α n).model.E.map (P.map (homOfLE h).op)).val.app U _)))
    rw [systemScalarModel_transpose_tmul, Equiv.apply_symm_apply, one_smul,
      systemScalarModel_map_tmul, SequenceProjection.transition_tmul, map_one,
      systemScalarModel_transpose_tmul, Equiv.apply_symm_apply, one_smul]
    exact hf.symm

private def extensionTowerAdjunction : extensionTower A B α ⊣ restrictionFunctor A B α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P N ↦
        { toFun := extensionTowerTranspose A B α
          invFun := extensionTowerUntranspose A B α
          left_inv := by intro f; apply strictRingSystem_hom_ext B; intro n
                         exact (scalar A B α n).ordinaryAdj.homEquiv _ _ |>.symm_apply_apply _
          right_inv := by intro f; apply NatTrans.ext; funext n
                          exact (scalar A B α n.unop).ordinaryAdj.homEquiv _ _
                            |>.apply_symm_apply _ }
      homEquiv_naturality_left_symm := by
        intro P Q N f g
        apply strictRingSystem_hom_ext B
        intro n
        exact (scalar A B α n).ordinaryAdj.homEquiv_naturality_left_symm (f.app (op n)) _
      homEquiv_naturality_right := by
        intro P N M f g
        apply NatTrans.ext
        funext n
        exact (scalar A B α n.unop).ordinaryAdj.homEquiv_naturality_right
          (f.app n.unop) (g.app n.unop) }

private def constantSystem (P : ℕᵒᵖ ⥤ Modules A) :
    StrictRingSystem ((Functor.const ℕᵒᵖ).obj A) where
  level n := P.obj (op n)
  transition h := P.map (homOfLE h).op ≫ (systemScalarRestrictionUnit (𝟙 A) rfl).inv.app _
  identity n U x := by
    change (P.map (𝟙 (op n))).val.app U x = x
    rw [P.map_id]
    rfl
  compose h k U x := by
    change (P.map (homOfLE (h.trans k)).op).val.app U x =
      (P.map (homOfLE h).op).val.app U ((P.map (homOfLE k).op).val.app U x)
    exact congrArg (fun f ↦ f.val.app U x)
      (P.map_comp (homOfLE k).op (homOfLE h).op)

private def constantSystemTowerIso (P : ℕᵒᵖ ⥤ Modules A) :
    (restrictionFunctor A ((Functor.const ℕᵒᵖ).obj A) (𝟙 _)).obj
      (constantSystem A P) ≅ P :=
  NatIso.ofComponents (fun n ↦ (systemScalarRestrictionUnit (𝟙 A) rfl).app (P.obj n))
    (by intro n m f; ext U x; rfl)

private def constantSystemFunctor : (ℕᵒᵖ ⥤ Modules A) ⥤
    StrictRingSystem ((Functor.const ℕᵒᵖ).obj A) where
  obj := constantSystem A
  map f :=
    { app := fun n ↦ f.app (op n)
      comm := by
        intro m n h
        ext U x
        exact congrArg (fun g ↦ g.val.app U x) (f.naturality (homOfLE h).op).symm }
  map_id _ := by apply strictRingSystem_hom_ext; intro n; rfl
  map_comp _ _ := by apply strictRingSystem_hom_ext; intro n; rfl

private instance constantSystemFunctor_additive : (constantSystemFunctor A).Additive where
  map_add := by
    intro P Q f g
    apply strictRingSystem_hom_ext
    intro n
    exact ((systemEvaluation ((Functor.const ℕᵒᵖ).obj A) n).map_add
      (f := (constantSystemFunctor A).map f) (g := (constantSystemFunctor A).map g)).symm

private def constantSystemFunctorIso :
    constantSystemFunctor A ⋙
        restrictionFunctor A ((Functor.const ℕᵒᵖ).obj A) (𝟙 _) ≅ 𝟭 _ :=
  NatIso.ofComponents (constantSystemTowerIso A) (by intros; ext n U x; rfl)

private theorem tower_kFlatResolution (X : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ) :
    ∃ (P : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ) (f : P ⟶ X),
      (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients (R := A)
        (P.asFunctor.obj (op n))) ∧ QuasiIso f := by
  let B₀ := (Functor.const ℕᵒᵖ).obj A
  let U₀ := restrictionFunctor A B₀ (𝟙 _)
  let := (restrictionFunctor_exact A B₀ (𝟙 _)).1
  let := (restrictionFunctor_exact A B₀ (𝟙 _)).2
  obtain ⟨L, f, hL, hf⟩ := strictRingSystem_kFlatResolution B₀
    (((constantSystemFunctor A).mapHomologicalComplex (.up ℤ)).obj X)
  have : QuasiIso f := hf
  let P := (U₀.mapHomologicalComplex (.up ℤ)).obj L
  let e := (NatIso.mapHomologicalComplex (constantSystemFunctorIso A) (.up ℤ)).app X
  refine ⟨P, (U₀.mapHomologicalComplex (.up ℤ)).map f ≫ e.hom, ?_, by infer_instance⟩
  intro n
  let en := (NatIso.mapHomologicalComplex
    (systemScalarRestrictionUnit (𝟙 A) rfl) (.up ℤ)).app
      (((systemEvaluation B₀ n).mapHomologicalComplex (.up ℤ)).obj L)
  exact kFlat_iso_independent A en.symm (hL n).1

section LocalizationHelpers
universe a₁ a₂ b₁ b₂ q₁ q₂ q₃
variable {D : Type a₁} [Category.{a₂} D] [Abelian D] [HasDerivedCategory.{q₁} D]
  {E : Type b₁} [Category.{b₂} E] [Abelian E] [HasDerivedCategory.{q₂} E]

-- The comparison needs the adjunction as data, but never computes its unit.
-- Choice from this proved proposition keeps that construction out of reductions.
private theorem homotopyAdjunction_nonempty
    (F : D ⥤ E) (G : E ⥤ D) [F.Additive] [G.Additive] (adj : F ⊣ G) :
    Nonempty (F.mapHomotopyCategory (.up ℤ) ⊣ G.mapHomotopyCategory (.up ℤ)) :=
  ⟨adj.mapHomotopyCategory (.up ℤ)⟩

private theorem homotopy_inverts (F : D ⥤ E) [F.Additive]
    (P : CochainComplex D ℤ → Prop)
    (hF : ∀ {X Y : CochainComplex D ℤ}, P X → P Y → ∀ f : X ⟶ Y,
      QuasiIso f → QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)) :
    ∀ {X Y : HomotopyCategory D (.up ℤ)}, P X.as → P Y.as → ∀ f : X ⟶ Y,
      IsIso (DerivedCategory.Qh.map f) →
        IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map f)) := by
  intro X Y hX hY f hf
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  have hq : QuasiIso f :=
    (HomologicalComplex.mem_quasiIso_iff _).mp
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
        ((DerivedCategory.isIso_Qh_map_iff _).mp hf))
  apply (DerivedCategory.isIso_Qh_map_iff _).mpr
  rw [F.mapHomotopyCategory_map]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
    ((HomologicalComplex.mem_quasiIso_iff _).mpr (hF hX hY f hq))
private theorem limit_adjunction_quasiIso
    [HasLimitsOfShape ℕᵒᵖ E] [(lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive]
    [HasDerivedCategory.{q₃} (ℕᵒᵖ ⥤ E)]
    (F : D ⥤ (ℕᵒᵖ ⥤ E)) (L : (ℕᵒᵖ ⥤ E) ⥤ D)
    [F.Additive] [L.Additive] (adj : L ⊣ F)
    (P : CochainComplex E ℤ → Prop)
    (resE : ∀ X : CochainComplex E ℤ, ∃ (Y : CochainComplex E ℤ) (f : Y ⟶ X),
      P Y ∧ QuasiIso f)
    (resB : ∀ X : CochainComplex (ℕᵒᵖ ⥤ E) ℤ,
      ∃ (Y : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) (f : Y ⟶ X),
        (∀ n : ℕ, P (Y.asFunctor.obj (op n))) ∧ QuasiIso f)
    (hinv : ∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ E) ℤ},
      (∀ n : ℕ, P (X.asFunctor.obj (op n))) →
      (∀ n : ℕ, P (Y.asFunctor.obj (op n))) → ∀ f : X ⟶ Y,
        QuasiIso f → QuasiIso ((L.mapHomologicalComplex (.up ℤ)).map f))
    {I : CochainComplex D ℤ} [I.IsKInjective]
    {T : CochainComplex (ℕᵒᵖ ⥤ E) ℤ} [T.IsKInjective]
    (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j] :
    QuasiIso (((lim : (ℕᵒᵖ ⥤ E) ⥤ E).mapHomologicalComplex (.up ℤ)).map j) := by
  let PB : ObjectProperty (HomotopyCategory (ℕᵒᵖ ⥤ E) (.up ℤ)) := fun X ↦
    ∀ n : ℕ, P (X.as.asFunctor.obj (op n))
  let PE : ObjectProperty (HomotopyCategory E (.up ℤ)) := fun X ↦
    P X.as
  let CT := (Functor.const ℕᵒᵖ : E ⥤ (ℕᵒᵖ ⥤ E))
  let LT := (lim : (ℕᵒᵖ ⥤ E) ⥤ E)
  have : CT.Additive := { map_add := by intros; rfl }
  have hresB : ∀ X, ∃ (P : _) (f : P ⟶ X), PB P ∧
      IsIso (DerivedCategory.Qh.map f) := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, f, hP, hf⟩ := resB X
    refine ⟨(HomotopyCategory.quotient _ _).obj P,
      (HomotopyCategory.quotient _ _).map f, hP, ?_⟩
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using hf
  have hresE : ∀ X, ∃ (P : _) (f : P ⟶ X), PE P ∧
      IsIso (DerivedCategory.Qh.map f) := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, f, hP, hf⟩ := resE X
    refine ⟨(HomotopyCategory.quotient _ _).obj P,
      (HomotopyCategory.quotient _ _).map f, hP, ?_⟩
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using hf
  have hIs : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ E) (.up ℤ)).map j)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using (inferInstance : QuasiIso j)
  have hconst : ∀ {X Y : HomotopyCategory E (.up ℤ)},
      PE X → PE Y → ∀ f : X ⟶ Y, IsIso (DerivedCategory.Qh.map f) →
        IsIso (DerivedCategory.Qh.map ((CT.mapHomotopyCategory (.up ℤ)).map f)) :=
    homotopy_inverts CT
    (fun X ↦ P X)
    (fun {_ _} _ _ f hf ↦ (HomologicalComplex.quasiIso_iff_evaluation _).mpr
      (fun _ ↦ hf))
  have hm : IsIso (DerivedCategory.Qh.map
      ((LT.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ E) (.up ℤ)).map j))) :=
    isIso_map_of_adjoints
    (homotopyAdjunction_nonempty L F adj).some
    (homotopyAdjunction_nonempty CT LT constLimAdj).some
    (HomotopyCategory.quasiIso (ℕᵒᵖ ⥤ E) (.up ℤ))
    (HomotopyCategory.quasiIso E (.up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh PB PE hresB hresE
    (homotopy_inverts L
      (fun X ↦ ∀ n : ℕ, P (X.asFunctor.obj (op n))) hinv)
    hconst (fun _ hX _ ↦ hX)
    ((HomotopyCategory.quotient D (.up ℤ)).obj I)
    (fun X ↦ CochainComplex.IsKInjective.Qh_map_bijective X I)
    ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ E) (.up ℤ)).obj T)
    (fun X ↦ CochainComplex.IsKInjective.Qh_map_bijective X T)
    ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ E) (.up ℤ)).map j)
  rw [LT.mapHomotopyCategory_map] at hm
  exact (HomologicalComplex.mem_quasiIso_iff _).mp
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
      ((DerivedCategory.isIso_Qh_map_iff _).mp hm))

end LocalizationHelpers

variable [HasDerivedCategory.{d} (Modules A)]

private theorem extensionTower_preserves
    {X Y : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ}
    (hX : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients (R := A)
      (X.asFunctor.obj (op n)))
    (hY : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients (R := A)
      (Y.asFunctor.obj (op n))) (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso (((extensionTower A B α).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (strictRingSystem_quasiIso_iff B _).mpr
  intro n
  exact (scalar A B α n).model.preserves (componentMap A f n) (hX n) (hY n)
    ((HomologicalComplex.quasiIso_iff_evaluation f).mp hf (op n))

attribute [local irreducible] extensionTower constantSystemFunctor
  extensionTowerAdjunction extensionTowerObj extensionTowerMap
  extensionTowerTranspose extensionTowerUntranspose

private theorem limit_restricted_quasiIso
    [HasDerivedCategory.{s} (StrictRingSystem B)]
    [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ Modules A)]
    {I : CochainComplex (StrictRingSystem B) ℤ} [I.IsKInjective]
    {T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ} [T.IsKInjective]
    (j : (restrictionComplex A B α).obj I ⟶ T) [QuasiIso j] :
    QuasiIso ((limitComplex A).map j) := by
  apply limit_adjunction_quasiIso (restrictionFunctor A B α) (extensionTower A B α)
    (extensionTowerAdjunction A B α)
    (fun X ↦ CochainComplex.IsKFlatIndependentCoefficients (R := A) X)
    ?_ (tower_kFlatResolution A) (extensionTower_preserves A B α) j
  intro X
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A) X
  exact ⟨P, f, hP, hf⟩

private theorem projection_naturality
    {S T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ} (f : S ⟶ T) (n : ℕ) :
    (limitComplex A).map f ≫ projection A T n = projection A S n ≫ componentMap A f n := by
  exact (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).naturality f

attribute [local irreducible] restrictionFunctor tower projection

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A restricted system resolution is acyclic for inverse limit, and its actual
projections satisfy the two-resolution cancellation equation in D(A).
Source: Stacks 0D6E and 0940
(blueprint: lem-coef-restricted-tower-resolution-acyclicity).

Proof: steps 1--4 of the node. The constructed direct image is g_*r_*=lim U0.
Use the resolving-adjunction comparison underlying the ringed-topos composition
lemma. The left adjoint of restriction extends scalars levelwise, and constant
towers are left adjoint to limit. Resolve towers on the constant-ring sequence site.
Their components are K-flat, so scalar extension inverts quasi-isomorphisms between
these representatives; constant towers preserve K-flatness. The K-injective Hom
bijections then imply that lim j is a quasi-isomorphism. Evaluation and restriction
are exact, so the components of U0a and j are quasi-isomorphisms. Localize the chain-map equality
pr_n^T ∘ lim j = j_n ∘ pr_n^(U0I), then cancel j_n and U0a_n.
The isomorphisms ea and ej have exactly these localized maps as their homs, so
there is no choice of comparison hidden in their inverses. -/
theorem acyclicity
    {N I : CochainComplex (StrictRingSystem B) ℤ} (a : N ⟶ I)
    [QuasiIso a] [I.IsKInjective]
    {T : CochainComplex (ℕᵒᵖ ⥤ Modules A) ℤ}
    (j : (restrictionComplex A B α).obj I ⟶ T) [QuasiIso j] [T.IsKInjective] :
    QuasiIso ((limitComplex A).map j) ∧
    ∀ n : ℕ,
      QuasiIso (componentMap A ((restrictionComplex A B α).map a) n) ∧
      QuasiIso (componentMap A j n) ∧
      ∃ (ea : DerivedCategory.Q.obj
          (((restrictionComplex A B α).obj N).asFunctor.obj (op n)) ≅
          DerivedCategory.Q.obj
            (((restrictionComplex A B α).obj I).asFunctor.obj (op n)))
        (ej : DerivedCategory.Q.obj
          (((restrictionComplex A B α).obj I).asFunctor.obj (op n)) ≅
          DerivedCategory.Q.obj (T.asFunctor.obj (op n))),
        ea.hom = DerivedCategory.Q.map
          (componentMap A ((restrictionComplex A B α).map a) n) ∧
        ej.hom = DerivedCategory.Q.map (componentMap A j n) ∧
        DerivedCategory.Q.map ((limitComplex A).map j) ≫
            DerivedCategory.Q.map (projection A T n) ≫ ej.inv ≫ ea.inv =
          DerivedCategory.Q.map (projection A ((restrictionComplex A B α).obj I) n) ≫
            ea.inv := by
  let := (restrictionFunctor_exact A B α).1
  let := (restrictionFunctor_exact A B α).2
  let := HasDerivedCategory.standard (StrictRingSystem B)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Modules A)
  refine ⟨limit_restricted_quasiIso A B α j, ?_⟩
  intro n
  have ha : QuasiIso (componentMap A ((restrictionComplex A B α).map a) n) :=
    (HomologicalComplex.quasiIso_iff_evaluation
      ((restrictionComplex A B α).map a)).mp inferInstance (op n)
  have hj : QuasiIso (componentMap A j n) :=
    (HomologicalComplex.quasiIso_iff_evaluation j).mp inferInstance (op n)
  let ea := asIso (DerivedCategory.Q.map
    (componentMap A ((restrictionComplex A B α).map a) n))
  let ej := asIso (DerivedCategory.Q.map (componentMap A j n))
  refine ⟨ha, hj, ea, ej, rfl, rfl, ?_⟩
  rw [← Functor.map_comp_assoc, projection_naturality, Functor.map_comp]
  change (_ ≫ ej.hom) ≫ ej.inv ≫ ea.inv = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]

section IsoTransport
universe x₁ x₂
variable {V : Type x₁} [Category.{x₂} V]

end IsoTransport

section HomotopyComparison
universe ca cv da dv q
variable {D : Type ca} [Category.{cv} D] [Abelian D] [HasDerivedCategory.{q} D]
  {E : Type da} [Category.{dv} E] [Abelian E]

end HomotopyComparison

variable [HasDerivedCategory.{s} (StrictRingSystem B)]
  [HasDerivedCategory.{t} (ℕᵒᵖ ⥤ Modules A)]

end SheafOfModules.RestrictedTowerResolution
