/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
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

/-!
# Coefficient restriction and direct image on derived diagram topoi

Source: Stacks Project, Cohomology on Sites, Tag 0D6E,
lemma-derived-pushforward-composition, applied on the small diagram sites
(blueprint: lem-pur-diagram-ring-restriction-pushforward).

Ring diagrams are represented by ring sheaves on `diagramSiteTopology J C K`.
Their module sheaves have precisely the semilinear horizontal transition maps.
The helpers below transport the componentwise geometric adjunction to those sites.
The final equation characterizes the comparison through the common composite:
its two sides are the two derived composition units, after termwise scalar restriction.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

/-- Forget module structure to the underlying sheaf of sets on a diagram site.
This is only the composite of the existing forgetful functors.
Source: Stacks Project, Modules on Sites, Tag 03DA
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
noncomputable abbrev diagramCoefficientUnderlying
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u}) :=
  SheafOfModules.toSheaf.{u} R ⋙ sheafCompose K (forget AddCommGrpCat)

section

set_option backward.isDefEq.respectTransparency false

-- Cache standard sheaf instances once: their repeated search dominates elaboration.
private theorem coefficientSheafify
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    HasSheafify K AddCommGrpCat.{u} := inferInstance

private theorem coefficientLocallyBijective
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance

private noncomputable abbrev coefficientSMul
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u}) (M : ringedSiteModules.{u} R) (U : Cᵒᵖ) :
    SMul (((sheafCompose K (forget RingCat)).obj R).obj.obj U) (M.val.obj U) :=
  inferInstanceAs (SMul (R.obj.obj U) (M.val.obj U))

attribute [local instance] coefficientSheafify
  coefficientLocallyBijective coefficientSMul

private noncomputable def linearOperation
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {R : Sheaf K RingCat.{u}} (M : ringedSiteModules.{u} R)
    (T : Sheaf K (Type u))
    (a : T ⟶ (sheafCompose K (forget RingCat)).obj R)
    (x y : T ⟶ (diagramCoefficientUnderlying R).obj M) :
    T ⟶ (diagramCoefficientUnderlying R).obj M :=
  ⟨{ app := fun U ↦ ↾(fun t ↦ (a.hom.app U t) •
        (show M.val.obj U from x.hom.app U t) + (show M.val.obj U from y.hom.app U t))
     naturality := by
       intro U V f
       ext t
       have ha := CategoryTheory.congr_fun (a.hom.naturality f) t
       have hx := CategoryTheory.congr_fun (x.hom.naturality f) t
       have hy := CategoryTheory.congr_fun (y.hom.naturality f) t
       change _ = M.val.map f (_ + _)
       rw [(M.val.map f).hom.map_add, M.val.map_smul]
       change a.hom.app V (T.obj.map f t) = (R.obj.map f).hom (a.hom.app U t) at ha
       change x.hom.app V (T.obj.map f t) = M.val.map f (x.hom.app U t) at hx
       change y.hom.app V (T.obj.map f t) = M.val.map f (y.hom.app U t) at hy
       exact congrArg₂ (fun (v w : M.val.obj V) ↦ v + w)
         (congrArg₂ (fun (r : R.obj.obj V) (z : M.val.obj V) ↦ r • z) ha hx) hy }⟩

private theorem ordinaryCoefficientComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {AX BX : Sheaf K RingCat.{u}} {AY BY : Sheaf L RingCat.{u}}
    (aX : AX ⟶ BX) (aY : AY ⟶ BY)
    (f : RingedToposMorphism BX BY) (g : RingedToposMorphism AX AY)
    (hInv : f.inverse = g.inverse) (hDir : f.direct = g.direct)
    (hAdj : HEq f.adj g.adj)
    (hRing : f.inverse.map ((sheafCompose L (forget RingCat)).map aY) ≫ f.ringMap =
      eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose L (forget RingCat)).obj AY)) hInv) ≫
        g.ringMap ≫ (sheafCompose K (forget RingCat)).map aX) :
    ∃ c : f.modules ⋙ SheafOfModules.restrictScalars.{u} aY ≅
        SheafOfModules.restrictScalars.{u} aX ⋙ g.modules,
      ∀ M : ringedSiteModules.{u} BX,
        (diagramCoefficientUnderlying AY).map (c.hom.app M) ≫
            g.underlying.hom.app ((SheafOfModules.restrictScalars.{u} aX).obj M) =
          f.underlying.hom.app M ≫
            eqToHom (congrArg (fun H ↦ H.obj ((diagramCoefficientUnderlying BX).obj M)) hDir) := by
  classical
  rcases f with ⟨F, G, adj, hF, p, hp0, hp1, hpadd, hpmul, H, hH, eH, hlinH⟩
  rcases g with ⟨F', G', adj', hF', q, hq0, hq1, hqadd, hqmul, I, hI, eI, hlinI⟩
  dsimp only at hInv hDir hAdj hRing ⊢
  subst F'
  subst G'
  cases hAdj
  simp only [eqToHom_refl, Category.id_comp] at hRing
  let resX := SheafOfModules.restrictScalars.{u} aX
  let resY := SheafOfModules.restrictScalars.{u} aY
  let α (M : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying AY).obj (resY.obj (H.obj M)) ≅
        (diagramCoefficientUnderlying AY).obj (I.obj (resX.obj M)) :=
    eH.app M ≪≫ (eI.app (resX.obj M)).symm
  have hα (M : ringedSiteModules.{u} BX) :
      (α M).hom ≫ eI.hom.app (resX.obj M) = eH.hom.app M := by
    change (eH.hom.app M ≫ eI.inv.app (resX.obj M)) ≫ eI.hom.app (resX.obj M) = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ eH.hom.app M ≫ k) (eI.inv_hom_id_app (resX.obj M))).trans
        (Category.comp_id _))
  have hlinear (M : ringedSiteModules.{u} BX) (T : Sheaf L (Type u))
      (a : T ⟶ (sheafCompose L (forget RingCat)).obj AY)
      (x y : T ⟶ (diagramCoefficientUnderlying AY).obj (resY.obj (H.obj M))) :
      linearOperation (resY.obj (H.obj M)) T a x y ≫ (α M).hom =
        linearOperation (I.obj (resX.obj M)) T a (x ≫ (α M).hom) (y ≫ (α M).hom) := by
    apply (cancel_mono (eI.hom.app (resX.obj M))).mp
    apply (adj.homEquiv T ((diagramCoefficientUnderlying BX).obj M)).symm.injective
    rw [Category.assoc, hα]
    ext U t
    have hb := hlinH M T (a ≫ (sheafCompose L (forget RingCat)).map aY)
      x y (linearOperation (resY.obj (H.obj M)) T a x y) (fun _ _ ↦ rfl) U t
    have hs := hlinI (resX.obj M) T a (x ≫ (α M).hom) (y ≫ (α M).hom)
      (linearOperation (I.obj (resX.obj M)) T a (x ≫ (α M).hom) (y ≫ (α M).hom))
      (fun _ _ ↦ rfl) U t
    have hr : F.map (a ≫ (sheafCompose L (forget RingCat)).map aY) ≫ p =
        (F.map a ≫ q) ≫ (sheafCompose K (forget RingCat)).map aX := by
      rw [F.map_comp, Category.assoc, hRing, Category.assoc]
    simp only [Category.assoc, hα] at hs
    rw [hr] at hb
    exact hb.trans hs.symm
  let one (T : Sheaf L (Type u)) : T ⟶ (sheafCompose L (forget RingCat)).obj AY :=
    ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : AY.obj.obj U))
       naturality := by intro U V f; ext t; exact (AY.obj.map f).hom.map_one.symm }⟩
  have hadd (M : ringedSiteModules.{u} BX) (U : Dᵒᵖ)
      (x y : (resY.obj (H.obj M)).val.obj U) :
      (α M).hom.hom.app U (x + y) =
        (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U x) +
          (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U y) := by
    let X := (diagramCoefficientUnderlying AY).obj (resY.obj (H.obj M))
    have hh := congrArg (fun f ↦ f.hom.app U (x, y))
      (hlinear M (X ⊗ X) (one _) (CartesianMonoidalCategory.fst X X)
        (CartesianMonoidalCategory.snd X X))
    change (α M).hom.hom.app U ((1 : AY.obj.obj U) • x + y) =
      (1 : AY.obj.obj U) •
        (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U x) +
          (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U y) at hh
    simpa only [one_smul] using hh
  have hsmul (M : ringedSiteModules.{u} BX) (U : Dᵒᵖ)
      (r : AY.obj.obj U) (x : (resY.obj (H.obj M)).val.obj U) :
      (α M).hom.hom.app U (r • x) = r •
        (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U x) := by
    let X := (diagramCoefficientUnderlying AY).obj (resY.obj (H.obj M))
    let R := (sheafCompose L (forget RingCat)).obj AY
    let z : R ⊗ X ⟶ X :=
      ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : (resY.obj (H.obj M)).val.obj U))
         naturality := by
           intro U V f
           ext t
           exact ((resY.obj (H.obj M)).val.map f).hom.map_zero.symm }⟩
    have hh := congrArg (fun f ↦ f.hom.app U (r, x))
      (hlinear M (R ⊗ X) (CartesianMonoidalCategory.fst R X)
        (CartesianMonoidalCategory.snd R X) z)
    have hzero : (α M).hom.hom.app U (0 : (resY.obj (H.obj M)).val.obj U) =
        (0 : (I.obj (resX.obj M)).val.obj U) := by
      have hz := hadd M U 0 0
      exact (@add_eq_left ((I.obj (resX.obj M)).val.obj U)
        inferInstance inferInstance _ _).mp (by simpa only [zero_add] using hz.symm)
    change (α M).hom.hom.app U (r • x + 0) = r •
      (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U x) +
        (show (I.obj (resX.obj M)).val.obj U from
          (α M).hom.hom.app U (0 : (resY.obj (H.obj M)).val.obj U)) at hh
    simpa only [add_zero, hzero] using hh
  let f (M : ringedSiteModules.{u} BX) : resY.obj (H.obj M) ⟶ I.obj (resX.obj M) :=
    { val :=
        { app := fun U ↦ @ModuleCat.ofHom (AY.obj.obj U) inferInstance
            ((resY.obj (H.obj M)).val.obj U) ((I.obj (resX.obj M)).val.obj U)
            ((resY.obj (H.obj M)).val.obj U).isAddCommGroup
            ((resY.obj (H.obj M)).val.obj U).isModule
            ((I.obj (resX.obj M)).val.obj U).isAddCommGroup
            ((I.obj (resX.obj M)).val.obj U).isModule
            { toFun := (α M).hom.hom.app U
              map_add' := hadd M U
              map_smul' := hsmul M U }
          naturality := by
            intro U V h
            ext x
            exact CategoryTheory.congr_fun ((α M).hom.hom.naturality h) x } }
  have hf (M : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying AY).map (f M) = (α M).hom := rfl
  have hi (M : ringedSiteModules.{u} BX) : IsIso (f M) := by
    have : IsIso ((diagramCoefficientUnderlying AY).map (f M)) := by rw [hf]; infer_instance
    exact isIso_of_reflects_iso (f M) (diagramCoefficientUnderlying AY)
  let β : H ⋙ resY ⟶ resX ⋙ I :=
    { app := f
      naturality := by
        intro M N h
        apply (diagramCoefficientUnderlying AY).map_injective
        simp only [Functor.map_comp, hf]
        apply (cancel_mono (eI.hom.app (resX.obj N))).mp
        simp only [Category.assoc, hα]
        have hI' := eI.hom.naturality (resX.map h)
        have hH' := eH.hom.naturality h
        change (diagramCoefficientUnderlying AY).map (I.map (resX.map h)) ≫
            eI.hom.app (resX.obj N) = eI.hom.app (resX.obj M) ≫
              G.map ((diagramCoefficientUnderlying BX).map h) at hI'
        change (diagramCoefficientUnderlying AY).map (resY.map (H.map h)) ≫
            eH.hom.app N = eH.hom.app M ≫
              G.map ((diagramCoefficientUnderlying BX).map h) at hH'
        dsimp only [Functor.comp_map]
        erw [hI', ← Category.assoc, hα]
        exact hH' }
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨asIso β, ?_⟩
  intro M
  simp only [eqToHom_refl, Category.comp_id]
  exact hα M

private theorem coefficientRestriction_exact
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {R S : Sheaf K RingCat.{u}} (a : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} a) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} a) := by
  let r := SheafOfModules.restrictScalars.{u} a
  have : PreservesFiniteLimits (r ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S))
  have : PreservesFiniteColimits (r ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf S))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    reflectsFiniteColimitsOfReflectsIsomorphisms _
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves r (SheafOfModules.toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves r (SheafOfModules.toSheaf R)⟩

private theorem coefficientCommRingSheaf
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u})
    (hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a) :
    ∃ O : Sheaf K CommRingCat.{u},
      (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj O = R := by
  let obj (U : Cᵒᵖ) : CommRingCat.{u} :=
    { carrier := R.obj.obj U
      commRing := { (inferInstance : Ring (R.obj.obj U)) with mul_comm := hcomm U } }
  let Oc : Cᵒᵖ ⥤ CommRingCat.{u} :=
    { obj := obj
      map := fun {U V} g ↦
        @CommRingCat.ofHom (obj U) (obj V) (obj U).commRing (obj V).commRing
          (R.obj.map g).hom
      map_id := fun U ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (R.obj.map_id U)
      map_comp := fun g h ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (R.obj.map_comp g h) }
  have hO : Presheaf.IsSheaf K Oc := by
    apply Presheaf.isSheaf_of_isSheaf_comp K Oc (forget₂ CommRingCat RingCat)
    exact R.property
  exact ⟨⟨Oc, hO⟩, rfl⟩

private theorem derivedCoefficientComparison
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : A' ⥤ B') (x : A ⥤ A') (y : B ⥤ B')
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    (rX : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A')
    (rY : DerivedCategory.{w} B ⥤ DerivedCategory.{w} B')
    (phiX : DerivedCategory.Q.{w} ⋙ rX ≅
      x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w})
    (phiY : DerivedCategory.Q.{w} ⋙ rY ≅
      y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w})
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (RG : DerivedCategory.{w} A' ⥤ DerivedCategory.{w} B')
    (etaF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (etaG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RG)
    (hF : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (etaF.app I))
    (hG : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (etaG.app ((x.mapHomologicalComplex (.up ℤ)).obj I)))
    (c : F ⋙ y ≅ x ⋙ G) :
    ∃! kappa : RF ⋙ rY ≅ rX ⋙ RG,
      ∀ M : CochainComplex A ℤ,
        phiY.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
            rY.map (etaF.app M) ≫ kappa.hom.app (DerivedCategory.Q.{w}.obj M) =
          DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
            etaG.app ((x.mapHomologicalComplex (.up ℤ)).obj M) ≫ RG.map (phiX.inv.app M) := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let xc := x.mapHomologicalComplex (.up ℤ)
  let cc := NatIso.mapHomologicalComplex c (.up ℤ)
  -- Both units derive the same ordinary composite; exactness is encoded by phiX and phiY.
  let etaL : (F ⋙ y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (RF ⋙ rY) :=
    Functor.whiskerLeft Fc phiY.inv ≫ Functor.whiskerRight etaF rY
  let etaR : (F ⋙ y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (rX ⋙ RG) :=
    Functor.whiskerRight cc.hom DerivedCategory.Q.{w} ≫
      Functor.whiskerLeft xc etaG ≫ Functor.whiskerRight phiX.inv RG
  have hL : (RF ⋙ rY).IsRightDerivedFunctor etaL
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (derives (F ⋙ y)).isRightDerivedFunctor_of_isIso etaL
    intro I
    have := hF I.obj I.property
    change IsIso (phiY.inv.app (Fc.obj I.obj) ≫ rY.map (etaF.app I.obj))
    infer_instance
  have hR : (rX ⋙ RG).IsRightDerivedFunctor etaR
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (derives (F ⋙ y)).isRightDerivedFunctor_of_isIso etaR
    intro I
    have := hG I.obj I.property
    change IsIso (DerivedCategory.Q.map (cc.hom.app I.obj) ≫
      etaG.app (xc.obj I.obj) ≫ RG.map (phiX.inv.app I.obj))
    infer_instance
  let _ := hL
  let _ := hR
  let kappa := Functor.rightDerivedUnique (RF ⋙ rY) (rX ⋙ RG) etaL etaR
    (HomologicalComplex.quasiIso A (.up ℤ))
  have hkappa (M : CochainComplex A ℤ) :
      etaL.app M ≫ kappa.hom.app (DerivedCategory.Q.obj M) = etaR.app M := by
    simpa only [kappa, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Iso.refl, NatTrans.id_app, Category.id_comp] using
      (Functor.rightDerivedNatTrans_app (RF ⋙ rY) (rX ⋙ RG) etaL etaR
        (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _).hom M)
  refine ⟨kappa, ?_, ?_⟩
  · intro M
    simpa only [etaL, etaR, cc, Fc, xc, NatIso.mapHomologicalComplex,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] using hkappa M
  · intro k hk
    apply Iso.ext
    apply Functor.rightDerived_ext (RF ⋙ rY) etaL
      (HomologicalComplex.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext M
    change etaL.app M ≫ k.hom.app (DerivedCategory.Q.obj M) =
      etaL.app M ≫ kappa.hom.app (DerivedCategory.Q.obj M)
    rw [hkappa]
    simpa only [etaL, etaR, cc, Fc, xc, NatIso.mapHomologicalComplex,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] using hk M

private theorem coefficientAcyclicDerived
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R S : Sheaf K RingCat.{u}) (T : Sheaf L RingCat.{u})
    (hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (hS : ∀ (U : Cᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    (hT : ∀ (U : Dᵒᵖ) (a b : T.obj.obj U), a * b = b * a)
    (a : R ⟶ S) (f : RingedToposMorphism R T)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} T)] :
    ∃ (RF : DerivedCategory.{w} (ringedSiteModules.{u} R) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} T))
      (eta : f.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RF),
      RF.IsRightDerivedFunctor eta (HomologicalComplex.quasiIso
        (ringedSiteModules.{u} R) (.up ℤ)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} R) ℤ,
        I.IsKInjective → IsIso (eta.app I)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} S) ℤ,
        I.IsKInjective → IsIso (eta.app
          (((SheafOfModules.restrictScalars.{u} a).mapHomologicalComplex (.up ℤ)).obj I))) := by
  obtain ⟨OR, rfl⟩ := coefficientCommRingSheaf R hR
  obtain ⟨OS, rfl⟩ := coefficientCommRingSheaf S hS
  obtain ⟨OT, rfl⟩ := coefficientCommRingSheaf T hT
  let r := siteRestrictionRingedTopos a
  -- The composition unit detects acyclicity of restricted K-injectives.
  obtain ⟨Rr, RF, Rc, etar, eta, etac, hr, hf, hc, hI, hF, k, hk, -⟩ :=
    ringedToposDerivedPushforwardComposition K K L OS OR OT r f
  refine ⟨RF, eta, hf, hF, ?_⟩
  intro I hInj
  have : IsIso (etar.app I) := (hI I hInj).1
  have : IsIso (etac.app I) := (hI I hInj).2
  have hh : IsIso (eta.app ((r.modules.mapHomologicalComplex (.up ℤ)).obj I) ≫
      RF.map (etar.app I)) := by
    rw [← hk.1 I]
    infer_instance
  let := hh
  have hi : IsIso (eta.app ((r.modules.mapHomologicalComplex (.up ℤ)).obj I)) :=
    IsIso.of_isIso_comp_right _ (RF.map (etar.app I))
  exact hi

end

-- Keep the original interface, including hBY and hStructuralS, which this proof does not need.
end CategoryTheory
