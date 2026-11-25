/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
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
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
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
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
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

/-! # Derived adjunction for the ringed sequence projection

Source: Stacks Project, Cohomology on Sites, Tags 0940, 0941, 06YY, 07A6;
Modules on Sites, Tag 03D7; Derived Categories, Tags 09T5 and 0FND.
(blueprint: lem-coef-sequence-projection-derived-adjunction).

The ordinary functors are characterized by their tensor generators and limit
projections. The derived adjunction is normalized on every chain map, so localization
extends precisely this ordinary correspondence to fractions. Index `n` means level `n+1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w d

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequenceProjection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The existing module category over the base ring sheaf, with coefficient universe `w`.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-projection-derived-adjunction). -/
abbrev Modules (A : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)

/-- The actual restriction from level `n+1` along its specified structural ring map.
Source: Stacks 03D7 (blueprint: lem-coef-sequence-projection-derived-adjunction). -/
abbrev restriction (A : Sheaf J CommRingCat.{w})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) (n : ℕ) : systemLevel B n ⥤ Modules A :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (α.app (op n)))

/-- The image of the local tensor `b ⊗ x` in the existing sheafified scalar extension.
Source: Stacks 03EK (blueprint: lem-coef-sequence-projection-derived-adjunction).
The scalar-first convention is the symmetry of the node's notation `x ⊗ b`. -/
def tensorSection {A S : Sheaf J CommRingCat.{w}} (φ : A ⟶ S)
    (M : Modules A) (U : Cᵒᵖ) (b : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRings φ M).val.obj U :=
  @SMul.smul (S.obj.obj U) ((changeOfRings φ M).val.obj U) inferInstance b
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (M.val.obj U)) x))

private abbrev scalar (A : Sheaf J CommRingCat.{w})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) (n : ℕ) :=
  (nonempty_systemScalarModel (α.app (op n))).some

variable (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
  (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)

private def restrictionComp {m n : ℕ} (h : m ≤ n) :
    systemRestriction B h ⋙ restriction A B α n ≅ restriction A B α m :=
  systemScalarRestrictionComposition _ _ _ (by
    simpa using α.naturality (homOfLE h).op)

private def transition (M : Modules A) {m n : ℕ} (h : m ≤ n) :
    (scalar A B α n).model.E.obj M ⟶
      (systemRestriction B h).obj ((scalar A B α m).model.E.obj M) :=
  ((scalar A B α n).ordinaryAdj.homEquiv _ _).symm
    ((scalar A B α m).ordinaryAdj.unit.app M ≫
      (restrictionComp A B α h).inv.app _)

private theorem transition_tmul (M : Modules A) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U) :
    (transition A B α M h).val.app U
      (systemModelTmul (scalar A B α n).model M U b x) =
    systemModelTmul (scalar A B α m).model M U
      ((B.map (homOfLE h).op).hom.app U b) x := by
  rw [systemScalarModel_transpose_tmul, transition, Equiv.apply_symm_apply]
  change @SMul.smul ((B.obj (op m)).obj.obj U)
    (((scalar A B α m).model.E.obj M).val.obj U) inferInstance
    ((B.map (homOfLE h).op).hom.app U b)
    (((scalar A B α m).ordinaryAdj.unit.app M).val.app U x) = _
  rw [(scalar A B α m).unit_normalized]
  dsimp only [systemModelTmul]
  rw [one_smul]
  rfl

private def extensionObj (M : Modules A) : StrictRingSystem B where
  level n := (scalar A B α n).model.E.obj M
  transition h := transition A B α M h
  identity n U x := by
    let e := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op)
      (B.map_id (op n))
    have he : transition A B α M (Nat.le_refl n) = e.inv.app _ := by
      apply systemScalarModel_hom_ext (scalar A B α n)
      intro V y
      rw [transition_tmul]
      change systemModelTmul (scalar A B α n).model M V
        ((B.map (𝟙 (op n))).hom.app V 1) y = _
      rw [B.map_id]
      rfl
    exact congrArg (fun f ↦ f.val.app U x) he
  compose {l m n} h k U x := by
    let e := systemScalarRestrictionComposition (B.map (homOfLE k).op)
      (B.map (homOfLE h).op) (B.map (homOfLE (h.trans k)).op)
      (by rw [← B.map_comp]; rfl)
    have he : transition A B α M (h.trans k) =
        transition A B α M k ≫ (systemRestriction B k).map (transition A B α M h) ≫
          e.hom.app _ := by
      apply systemScalarModel_hom_ext (scalar A B α n)
      intro V y
      change (transition A B α M (h.trans k)).val.app V _ =
        (transition A B α M h).val.app V ((transition A B α M k).val.app V _)
      rw [transition_tmul, transition_tmul, transition_tmul, map_one, map_one, map_one]
    exact congrArg (fun f ↦ f.val.app U x) he

private def extensionMap {M M' : Modules A} (f : M ⟶ M') :
    extensionObj A B α M ⟶ extensionObj A B α M' where
  app n := (scalar A B α n).model.E.map f
  comm {m n} h := by
    apply systemScalarModel_hom_ext (scalar A B α n)
    intro U x
    change (transition A B α M' h).val.app U
      (((scalar A B α n).model.E.map f).val.app U _) =
      ((scalar A B α m).model.E.map f).val.app U ((transition A B α M h).val.app U _)
    rw [systemScalarModel_map_tmul, transition_tmul, transition_tmul,
      systemScalarModel_map_tmul]
    rfl

private theorem system_ext {M N : StrictRingSystem B} (f g : M ⟶ N)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

private def extension : Modules A ⥤ StrictRingSystem B where
  obj := extensionObj A B α
  map := extensionMap A B α
  map_id M := system_ext B _ _ (fun n ↦ (scalar A B α n).model.E.map_id M)
  map_comp f g := system_ext B _ _ (fun n ↦ (scalar A B α n).model.E.map_comp f g)

private instance extension_additive : (extension A B α).Additive where
  map_add {M N} f g := by
    apply system_ext B
    intro n
    change (scalar A B α n).model.E.map (f + g) = _
    rw [(scalar A B α n).model.E.map_add]
    exact ((systemEvaluation B n).map_add (f := (extension A B α).map f)
      (g := (extension A B α).map g)).symm

private def restrictedDiagram (N : StrictRingSystem B) : ℕᵒᵖ ⥤ Modules A where
  obj n := (restriction A B α n.unop).obj (N.level n.unop)
  map {n m} h := (restriction A B α n.unop).map (N.transition (leOfHom h.unop)) ≫
    (restrictionComp A B α (leOfHom h.unop)).hom.app _
  map_id n := by
    ext U x
    exact N.identity n.unop U x
  map_comp {n m l} h k := by
    ext U x
    exact N.compose (leOfHom k.unop) (leOfHom h.unop) U x

private def restrictedDiagrams : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ Modules A) where
  obj := restrictedDiagram A B α
  map {N N'} f :=
    { app := fun n ↦ (restriction A B α n.unop).map (f.app n.unop)
      naturality := by
        intro n m h
        ext U x
        exact (congrArg (fun t ↦ t.val.app U x) (f.comm (leOfHom h.unop))).symm }
  map_id N := by ext n U x; rfl
  map_comp f g := by ext n U x; rfl

private def directImage : StrictRingSystem B ⥤ Modules A :=
  restrictedDiagrams A B α ⋙ lim

private def projection (N : StrictRingSystem B) (n : ℕ) :
    (directImage A B α).obj N ⟶ (restriction A B α n).obj (N.level n) :=
  limit.π (restrictedDiagram A B α N) (op n)

private theorem projection_natural {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ) :
    (directImage A B α).map f ≫ projection A B α N' n =
      projection A B α N n ≫ (restriction A B α n).map (f.app n) :=
  limMap_π _ (op n)

private theorem projection_compatible (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (x : ((directImage A B α).obj N).val.obj U) :
    (projection A B α N m).val.app U x =
      (N.transition h).val.app U ((projection A B α N n).val.app U x) := by
  exact (congrArg (fun f ↦ f.val.app U x)
    (limit.w (restrictedDiagram A B α N) (homOfLE h).op)).symm

private def familyCone (M : Modules A) (N : StrictRingSystem B)
    (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n))
    (hf : ∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
      (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) :
    Cone (restrictedDiagram A B α N) where
  pt := M
  π :=
    { app := fun n ↦ f n.unop
      naturality := by
        intro n m h
        ext U x
        exact hf (leOfHom h.unop) U x }

private theorem projection_limit (M : Modules A) (N : StrictRingSystem B)
    (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n))
    (hf : ∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
      (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) :
    ∃! h : M ⟶ (directImage A B α).obj N, ∀ n : ℕ, h ≫ projection A B α N n = f n := by
  refine ⟨limit.lift _ (familyCone A B α M N f hf), fun n ↦ limit.lift_π _ _, ?_⟩
  intro h hh
  apply limit.hom_ext
  intro n
  exact (hh n.unop).trans (limit.lift_π (familyCone A B α M N f hf) n).symm

private def toFamily {M : Modules A} {N : StrictRingSystem B}
    (f : (extension A B α).obj M ⟶ N) (n : ℕ) :
    M ⟶ (restriction A B α n).obj (N.level n) :=
  (scalar A B α n).ordinaryAdj.homEquiv _ _ (f.app n)

private theorem toFamily_apply {M : Modules A} {N : StrictRingSystem B}
    (f : (extension A B α).obj M ⟶ N) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U) :
    (toFamily A B α f n).val.app U x =
      (f.app n).val.app U (systemModelTmul (scalar A B α n).model M U 1 x) := by
  rw [toFamily, Adjunction.homEquiv_unit]
  change (f.app n).val.app U (((scalar A B α n).ordinaryAdj.unit.app M).val.app U x) = _
  rw [(scalar A B α n).unit_normalized]

private theorem toFamily_compatible {M : Modules A} {N : StrictRingSystem B}
    (f : (extension A B α).obj M ⟶ N) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (toFamily A B α f m).val.app U x =
      (N.transition h).val.app U ((toFamily A B α f n).val.app U x) := by
  rw [toFamily_apply, toFamily_apply]
  have hc := congrArg (fun t ↦ t.val.app U
    (systemModelTmul (scalar A B α n).model M U 1 x)) (f.comm h)
  change (N.transition h).val.app U ((f.app n).val.app U _) =
    (f.app m).val.app U ((transition A B α M h).val.app U _) at hc
  rw [transition_tmul, map_one] at hc
  exact hc.symm

private def transpose {M : Modules A} {N : StrictRingSystem B}
    (f : (extension A B α).obj M ⟶ N) : M ⟶ (directImage A B α).obj N :=
  limit.lift _ (familyCone A B α M N (toFamily A B α f)
    (fun h ↦ toFamily_compatible A B α f h))

private theorem transpose_projection {M : Modules A} {N : StrictRingSystem B}
    (f : (extension A B α).obj M ⟶ N) (n : ℕ) :
    transpose A B α f ≫ projection A B α N n = toFamily A B α f n :=
  limit.lift_π _ _

private def untranspose {M : Modules A} {N : StrictRingSystem B}
    (h : M ⟶ (directImage A B α).obj N) : (extension A B α).obj M ⟶ N where
  app n := ((scalar A B α n).ordinaryAdj.homEquiv _ _).symm
    (h ≫ projection A B α N n)
  comm {m n} k := by
    apply systemScalarModel_hom_ext (scalar A B α n)
    intro U x
    change (N.transition k).val.app U
      (((scalar A B α n).ordinaryAdj.homEquiv _ _).symm
        (h ≫ projection A B α N n) |>.val.app U
          (systemModelTmul (scalar A B α n).model M U 1 x)) =
      (((scalar A B α m).ordinaryAdj.homEquiv _ _).symm
        (h ≫ projection A B α N m) |>.val.app U
          ((transition A B α M k).val.app U
            (systemModelTmul (scalar A B α n).model M U 1 x)))
    rw [transition_tmul, map_one, systemScalarModel_transpose_tmul,
      systemScalarModel_transpose_tmul, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, one_smul, one_smul]
    exact (projection_compatible A B α N k U (h.val.app U x)).symm

private def ordinaryHomEquiv (M : Modules A) (N : StrictRingSystem B) :
    ((extension A B α).obj M ⟶ N) ≃ (M ⟶ (directImage A B α).obj N) where
  toFun := transpose A B α
  invFun := untranspose A B α
  left_inv f := by
    apply system_ext B
    intro n
    apply ((scalar A B α n).ordinaryAdj.homEquiv M (N.level n)).injective
    change (scalar A B α n).ordinaryAdj.homEquiv _ _
      (((scalar A B α n).ordinaryAdj.homEquiv _ _).symm _) = _
    rw [Equiv.apply_symm_apply]
    exact transpose_projection A B α f n
  right_inv h := by
    apply limit.hom_ext (F := restrictedDiagram A B α N)
    intro n
    change transpose A B α (untranspose A B α h) ≫ projection A B α N n.unop =
      h ≫ projection A B α N n.unop
    rw [transpose_projection]
    exact Equiv.apply_symm_apply _ _

private def ordinaryAdjunction : extension A B α ⊣ directImage A B α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := ordinaryHomEquiv A B α
      homEquiv_naturality_left_symm := by
        intro M M' N f h
        apply system_ext B
        intro n
        change ((scalar A B α n).ordinaryAdj.homEquiv _ _).symm
          ((f ≫ h) ≫ projection A B α N n) =
          (scalar A B α n).model.E.map f ≫
            ((scalar A B α n).ordinaryAdj.homEquiv _ _).symm
              (h ≫ projection A B α N n)
        rw [Category.assoc]
        exact (scalar A B α n).ordinaryAdj.homEquiv_naturality_left_symm f _
      homEquiv_naturality_right := by
        intro M N N' f g
        apply limit.hom_ext (F := restrictedDiagram A B α N')
        intro n
        change transpose A B α (f ≫ g) ≫ projection A B α N' n.unop =
          (transpose A B α f ≫ (directImage A B α).map g) ≫
            projection A B α N' n.unop
        rw [transpose_projection, Category.assoc, projection_natural,
          ← Category.assoc, transpose_projection]
        exact (scalar A B α n.unop).ordinaryAdj.homEquiv_naturality_right
          (f.app n.unop) (g.app n.unop) }

private instance directImage_additive : (directImage A B α).Additive :=
  (ordinaryAdjunction A B α).right_adjoint_additive

private theorem extension_preserves {K L : CochainComplex (Modules A) ℤ}
    (f : K ⟶ L) (hK : K.IsKFlatIndependentCoefficients)
    (hL : L.IsKFlatIndependentCoefficients) (hf : QuasiIso f) :
    QuasiIso (((extension A B α).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (strictRingSystem_quasiIso_iff B _).2
  intro n
  exact (scalar A B α n).model.preserves f hK hL hf

private theorem flatResolution (K : CochainComplex (Modules A) ℤ) :
    ∃ (L : CochainComplex (Modules A) ℤ) (f : L ⟶ K),
      (L.IsKFlatIndependentCoefficients ∧ ∀ i : ℤ, (L.X i).IsFlatOnSite) ∧ QuasiIso f := by
  obtain ⟨L, f, hL, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A) K
  refine ⟨L, f, ⟨hL, fun i ↦ ?_⟩, hf⟩
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso A (L.X i)).symm (hflat i)

private theorem derivedPart
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (StrictRingSystem B)] :
    ∃ (L : DerivedCategory.{d} (Modules A) ⥤ DerivedCategory.{d} (StrictRingSystem B))
      (R : DerivedCategory.{d} (StrictRingSystem B) ⥤ DerivedCategory.{d} (Modules A))
      (ε : DerivedCategory.Q ⋙ L ⟶
        (extension A B α).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (η : (directImage A B α).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ R) (derivedAdj : L ⊣ R),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) ∧
      R.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) ∧
      (∀ Q : CochainComplex (Modules A) ℤ, Q.IsKFlatIndependentCoefficients →
        (∀ i : ℤ, (Q.X i).IsFlatOnSite) → IsIso (ε.app Q)) ∧
      (∀ I : CochainComplex (StrictRingSystem B) ℤ, I.IsKInjective → IsIso (η.app I)) ∧
      (∀ (P Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ P),
        Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
        QuasiIso q →
        ∃ c : L.obj (DerivedCategory.Q.obj P) ≅
          DerivedCategory.Q.obj (((extension A B α).mapHomologicalComplex (.up ℤ)).obj Q),
          L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q) ∧
      (∀ (Q : CochainComplex (Modules A) ℤ)
        (I : CochainComplex (StrictRingSystem B) ℤ)
        (f : ((extension A B α).mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
        derivedAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map
            (((ordinaryAdjunction A B α).mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
            η.app I) := by
  classical
  let G := extension A B α
  let F := directImage A B α
  let q := HomotopyCategory.quotient (Modules A) (.up ℤ)
  let H := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{d}
  let P : Set (HomotopyCategory (Modules A) (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex (Modules A) ℤ,
      (K.IsKFlatIndependentCoefficients ∧ ∀ i : ℤ, (K.X i).IsFlatOnSite) ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory (Modules A) (.up ℤ),
      ∃ (X' : HomotopyCategory (Modules A) (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso (Modules A) (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, hf⟩ := flatResolution A K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv : ∀ (X Y : HomotopyCategory (Modules A) (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso (Modules A) (.up ℤ) s →
        IsIso (H.map s) := by
    rintro X Y s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := extension_preserves A B α f hK.1 hL.1 hf
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (StrictRingSystem B) (.up ℤ)).map
        ((G.mapHomologicalComplex (.up ℤ)).map f)))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (StrictRingSystem B) (.up ℤ)) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨_, L, εh, hL, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass (Modules A) (DerivedCategory.{d} (StrictRingSystem B))
      H P hres hinv
  let := hL
  obtain ⟨ε, hε, hεapp⟩ := CategoryTheory.leftDerivedOnComplexes G
    (𝟭 (DerivedCategory.{d} (StrictRingSystem B))) L εh
  have hcomputes (Q : CochainComplex (Modules A) ℤ)
      (hk : Q.IsKFlatIndependentCoefficients) (hf : ∀ i : ℤ, (Q.X i).IsFlatOnSite) :
      IsIso (ε.app Q) := by
    rw [hεapp]
    exact hcomp (q.obj Q) ⟨Q, ⟨hk, hf⟩, rfl⟩
  let : IsGrothendieckAbelian.{w} (StrictRingSystem B) :=
    strictRingSystem_isGrothendieckAbelian B
  let : Abelian.HasKInjectiveResolutions (StrictRingSystem B) := inferInstance
  obtain ⟨R, η, hR, hη⟩ := CategoryTheory.exists_derived F
  obtain ⟨d, hd⟩ := derivedAdjunctionOfResolvingClass G F (ordinaryAdjunction A B α)
    P hres hinv L εh hL R η hR
  refine ⟨L, R, ε, η, d, hε, hR, hcomputes, hη, ?_, ?_⟩
  · intro K Q f hk hf hq
    have : QuasiIso f := hq
    have : IsIso (ε.app Q) := hcomputes Q hk hf
    let c := (asIso (L.map (DerivedCategory.Q.map f))).symm ≪≫ asIso (ε.app Q)
    exact ⟨c, by simp [c]⟩
  · intro Q I f
    rw [hεapp]
    exact hd Q I f

private def extensionIso (M : Modules A) (n : ℕ) :
    ((extension A B α).obj M).level n ≅ changeOfRings (α.app (op n)) M :=
  eqToIso ((scalar A B α n).model.obj_eq M)

private theorem extensionIso_tensor (M : Modules A) (n : ℕ) (U : Cᵒᵖ)
    (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U) :
    (extensionIso A B α M n).inv.val.app U (tensorSection (α.app (op n)) M U b x) =
      systemModelTmul (scalar A B α n).model M U b x := by
  exact ((extensionIso A B α M n).inv.val.app U).hom.map_smul b _

/-- The sequence projection has the canonical unbounded derived adjunction, its ordinary
limit direct image, and its simultaneous flat-term K-flat tensor model.
Source: Stacks 0940/0941, 06YY, 07A6, 03D7, 09T5 and 0FND
(blueprint: lem-coef-sequence-projection-derived-adjunction).

Proof plan:
1. Use `strictSystemSequenceEquivalence` (lem-pur-system-ringed-sequence-site).
Vertical covers give componentwise kernels, sheafified cokernels and quasi-isomorphisms
(situation-conventions).
2. The compatible families of sections form an A-module sheaf. Componentwise gluing
proves the limit universal property for the scalar restrictions (def-pc-sheaf-restrict-scalars).
3. Apply lem-weil-pbc-ringed-topoi-module-adjunction. At each level the tensor is the
sheafification of sectionwise scalar extension. The transpose of h sends b tensor x to
b times pi_n(h(x)); the inverse evaluates at 1 tensor x. These formulas are balanced,
natural, and compatible with the actual transitions of B.
4. Apply prop-pur-kinjective-resolutions-exist on the sequence site, then
lem-weil-pbc-kinjective-total-derived to obtain the universal right derived pair.
5. Apply lem-weil-pbc-ringed-topoi-derived-pullback and lem-pc-kflat-resolution.
One flat-term K-flat Q supplies every level, with transitions 1 tensor rho. The
left comparison is invertible on Q; its naturality gives the comparison for any
quasi-isomorphism Q to P and compatibility with all maps of representatives.
6. Apply lem-sfb-resolving-derived-adjunction-normalization to these universal pairs,
using lem-weil-pbc-termwise-adjunction-homotopy. Its chain-map normalization is the
last equation below. Naturality and inversion of quasi-isomorphisms extend that equation
to all derived fractions, including further denominators; no fixed representative is
assumed to represent every derived morphism by a chain map. -/
theorem derivedAdjunction
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    [HasDerivedCategory.{d} (Modules A)] [HasDerivedCategory.{d} (StrictRingSystem B)] :
    ∃ (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
      (_ : G.Additive) (_ : F.Additive)
      (e : ∀ (M : Modules A) (n : ℕ),
        (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
      (π : ∀ (N : StrictRingSystem B) (n : ℕ),
        F.obj N ⟶ (restriction A B α n).obj (N.level n))
      (adj : G ⊣ F),
      (∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
        (G.map f).app n ≫ (e M' n).hom =
          (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f) ∧
      (∀ (M : Modules A) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        ((G.obj M).transition h).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          (e M m).inv.val.app U (tensorSection (α.app (op m)) M U
            ((B.map (homOfLE h).op).hom.app U b) x)) ∧
      (∀ {N N' : StrictRingSystem B} (f : N ⟶ N') (n : ℕ),
        F.map f ≫ π N' n = π N n ≫ (restriction A B α n).map (f.app n)) ∧
      (∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
        (x : (F.obj N).val.obj U),
        (π N m).val.app U x =
          (N.transition h).val.app U ((π N n).val.app U x)) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B)
        (f : ∀ n : ℕ, M ⟶ (restriction A B α n).obj (N.level n)),
        (∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) (x : M.val.obj U),
          (f m).val.app U x = (N.transition h).val.app U ((f n).val.app U x)) →
        ∃! h : M ⟶ F.obj N, ∀ n : ℕ, h ≫ π N n = f n) ∧
      (∀ (M : Modules A) (N : StrictRingSystem B) (h : M ⟶ F.obj N)
        (n : ℕ) (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
        (((adj.homEquiv M N).symm h).app n).val.app U
            ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
            ((π N n).val.app U (h.val.app U x))) ∧
      ∃ (L : DerivedCategory.{d} (Modules A) ⥤ DerivedCategory.{d} (StrictRingSystem B))
        (R : DerivedCategory.{d} (StrictRingSystem B) ⥤ DerivedCategory.{d} (Modules A))
        (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (derivedAdj : L ⊣ R),
        L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules A) (.up ℤ)) ∧
        R.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ), Q.IsKFlatIndependentCoefficients →
          (∀ i : ℤ, (Q.X i).IsFlatOnSite) → IsIso (ε.app Q)) ∧
        (∀ (I : CochainComplex (StrictRingSystem B) ℤ), I.IsKInjective →
          IsIso (η.app I)) ∧
        (∀ (P Q : CochainComplex (Modules A) ℤ) (q : Q ⟶ P),
          Q.IsKFlatIndependentCoefficients → (∀ i : ℤ, (Q.X i).IsFlatOnSite) →
          QuasiIso q →
          ∃ c : L.obj (DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q),
            L.map (DerivedCategory.Q.map q) ≫ c.hom = ε.app Q) ∧
        (∀ (Q : CochainComplex (Modules A) ℤ)
          (I : CochainComplex (StrictRingSystem B) ℤ)
          (f : (G.mapHomologicalComplex (.up ℤ)).obj Q ⟶ I),
          derivedAdj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
              (ε.app Q ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
              η.app I) := by
  refine ⟨extension A B α, directImage A B α, inferInstance, inferInstance,
    extensionIso A B α, projection A B α, ordinaryAdjunction A B α,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M M' f n
    change (scalar A B α n).model.E.map f ≫
      eqToHom ((scalar A B α n).model.obj_eq M') = _
    rw [(scalar A B α n).model.map_eq]
    simp [extensionIso]
  · intro M m n h U b x
    rw [extensionIso_tensor, extensionIso_tensor]
    exact transition_tmul A B α M h U b x
  · exact fun f n ↦ projection_natural A B α f n
  · intro N m n h U x
    exact projection_compatible A B α N h U x
  · exact fun M N f hf ↦ projection_limit A B α M N f hf
  · intro M N h n U b x
    rw [extensionIso_tensor]
    simp only [ordinaryAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    have ht := systemScalarModel_transpose_tmul (scalar A B α n) M (N.level n)
      (((scalar A B α n).ordinaryAdj.homEquiv M (N.level n)).symm
        (h ≫ projection A B α N n)) U b x
    rw [Equiv.apply_symm_apply] at ht
    exact ht
  · exact derivedPart A B α

end SheafOfModules.SequenceProjection
