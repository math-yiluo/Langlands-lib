/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientScalarUnits
import all WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
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
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # The canonical inverse-image coefficient comparison

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-pur-coefficient-pullback-comparison).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

attribute [local instance] SheafOfModules.sheafHasBinaryProduct

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)

private def addMap {R : Sheaf J CommRingCat.{r}} (M : Mod J R) :
    (underlying R).obj M ⨯ (underlying R).obj M ⟶ (underlying R).obj M :=
  ⟨{ app := fun U ↦ ↾fun t ↦
        (show M.val.obj U from (prod.fst : _ ⟶ (underlying R).obj M).hom.app U t) +
        (show M.val.obj U from (prod.snd : _ ⟶ (underlying R).obj M).hom.app U t)
     naturality := by
       intro U V f
       ext t
       have h₁ := CategoryTheory.congr_fun
         ((prod.fst : (underlying R).obj M ⨯ (underlying R).obj M ⟶
           (underlying R).obj M).hom.naturality f) t
       have h₂ := CategoryTheory.congr_fun
         ((prod.snd : (underlying R).obj M ⨯ (underlying R).obj M ⟶
           (underlying R).obj M).hom.naturality f) t
       change _ = M.val.map f (_ + _)
       rw [map_add]
       exact congrArg₂ (· + ·) h₁ h₂ }⟩

private def smulMap {R : Sheaf J CommRingCat.{r}} (M : Mod J R) :
    (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
      (underlying R).obj M ⟶ (underlying R).obj M :=
  ⟨{ app := fun U ↦ ↾fun t ↦
        (show R.obj.obj U from (prod.fst : _ ⟶
          (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R).hom.app U t) •
        (show M.val.obj U from (prod.snd : _ ⟶ (underlying R).obj M).hom.app U t)
     naturality := by
       intro U V f
       ext t
       have h₁ := CategoryTheory.congr_fun
         ((prod.fst : (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
           (underlying R).obj M ⟶
           (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R).hom.naturality f) t
       have h₂ := CategoryTheory.congr_fun
         ((prod.snd : (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R ⨯
           (underlying R).obj M ⟶ (underlying R).obj M).hom.naturality f) t
       change _ = M.val.map f (_ • _)
       rw [M.val.map_smul]
       exact congrArg₂ (· • ·) h₁ h₂ }⟩

private def imagePair [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.obj (A ⨯ B)).obj.obj U :=
  (inv (prodComparison uInv A B)).hom.app U
    (SheafOfModules.sectionPair (uInv.obj A) (uInv.obj B) U x y)

omit [EssentiallySmall.{r} C] in
private theorem imagePair_fst [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.map (prod.fst : A ⨯ B ⟶ A)).hom.app U (imagePair A B U x y) = x := by
  change (inv (prodComparison uInv A B) ≫ uInv.map prod.fst).hom.app U _ = x
  rw [← prodComparison_fst, IsIso.inv_hom_id_assoc]
  exact SheafOfModules.sectionPair_fst _ _ _ _ _

omit [EssentiallySmall.{r} C] in
private theorem imagePair_snd [PreservesFiniteLimits uInv]
    (A B : Sheaf J (Type r)) (U : Xᵒᵖ)
    (x : (uInv.obj A).obj.obj U) (y : (uInv.obj B).obj.obj U) :
    (uInv.map (prod.snd : A ⨯ B ⟶ B)).hom.app U (imagePair A B U x y) = y := by
  change (inv (prodComparison uInv A B) ≫ uInv.map prod.snd).hom.app U _ = y
  rw [← prodComparison_snd, IsIso.inv_hom_id_assoc]
  exact SheafOfModules.sectionPair_snd _ _ _ _ _

private theorem underlying_restriction_map
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) {M N : Mod J S} (f : M ⟶ N) :
    (underlying R).map ((SuccessiveDerivedQuotient.restriction a).map f) =
      (underlying S).map f := rfl

private def restrictionUnderlying {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : Mod J S) :
    (underlying (g.rings.obj R)).obj
        ((g.inverse R).modules.obj ((SuccessiveDerivedQuotient.restriction a).obj M)) ≅
      (underlying (g.rings.obj R)).obj
        ((SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj
          ((g.inverse S).modules.obj M)) :=
  (g.inverse R).moduleUnderlying.app
    ((SuccessiveDerivedQuotient.restriction a).obj M) ≪≫
      ((g.inverse S).moduleUnderlying.app M).symm

private theorem restrictionUnderlying_add [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) (U : Xᵒᵖ)
    (x y : ((g.inverse R).modules.obj
      ((SuccessiveDerivedQuotient.restriction a).obj M)).val.obj U) :
    (restrictionUnderlying g a M).hom.hom.app U (x + y) =
      (show ((g.inverse S).modules.obj M).val.obj U from
        (restrictionUnderlying g a M).hom.hom.app U x) +
      (show ((g.inverse S).modules.obj M).val.obj U from
        (restrictionUnderlying g a M).hom.hom.app U y) := by
  let N := (SuccessiveDerivedQuotient.restriction a).obj M
  let A := (underlying S).obj M
  let e := (g.inverse R).moduleUnderlying.app N
  let p := imagePair A A U (e.hom.hom.app U x) (e.hom.hom.app U y)
  have hR := (g.inverse R).moduleAdd N (A ⨯ A) prod.fst prod.snd (addMap M)
    (fun _ _ ↦ rfl) U p
  have hS := (g.inverse S).moduleAdd M (A ⨯ A) prod.fst prod.snd (addMap M)
    (fun _ _ ↦ rfl) U p
  have hx : (e.inv).hom.app U ((uInv.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p) = x := by
    rw [imagePair_fst]
    exact congrArg (fun k ↦ k.hom.app U x) e.hom_inv_id
  have hy : (e.inv).hom.app U ((uInv.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p) = y := by
    rw [imagePair_snd]
    exact congrArg (fun k ↦ k.hom.app U y) e.hom_inv_id
  dsimp only [id] at hR hS
  change e.inv.hom.app U ((uInv.map (addMap M)).hom.app U p) =
    (show ((g.inverse R).modules.obj N).val.obj U from
      e.inv.hom.app U ((uInv.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p)) +
    (show ((g.inverse R).modules.obj N).val.obj U from
      e.inv.hom.app U ((uInv.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p)) at hR
  have hR' := hR.trans (congrArg₂ (· + ·) hx hy)
  let f : ((g.inverse R).modules.obj N).val.obj U →
      ((g.inverse S).modules.obj M).val.obj U := fun z ↦
    ((g.inverse S).moduleUnderlying.inv.app M).hom.app U (e.hom.hom.app U z)
  have h := congrArg f hR'
  have hc : f (e.inv.hom.app U ((uInv.map (addMap M)).hom.app U p)) =
      ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
        ((uInv.map (addMap M)).hom.app U p) :=
    congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z)
      (congrArg (fun k ↦ k.hom.app U ((uInv.map (addMap M)).hom.app U p)) e.inv_hom_id)
  change ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
      ((uInv.map (addMap M)).hom.app U p) =
    (show ((g.inverse S).modules.obj M).val.obj U from
      ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
        ((uInv.map (prod.fst : A ⨯ A ⟶ A)).hom.app U p)) +
    (show ((g.inverse S).modules.obj M).val.obj U from
      ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
        ((uInv.map (prod.snd : A ⨯ A ⟶ A)).hom.app U p)) at hS
  have hS' := hS.trans (congrArg₂ (· + ·)
    (congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z)
      (imagePair_fst A A U _ _))
    (congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z)
      (imagePair_snd A A U _ _)))
  change f (x + y) = f x + f y
  exact h.symm.trans (hc.trans hS')

private theorem restrictionUnderlying_smul [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) (U : Xᵒᵖ)
    (t : (g.rings.obj R).obj.obj U)
    (x : ((g.inverse R).modules.obj
      ((SuccessiveDerivedQuotient.restriction a).obj M)).val.obj U) :
    (restrictionUnderlying g a M).hom.hom.app U (t • x) =
      t • (show ((SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj
        ((g.inverse S).modules.obj M)).val.obj U from
          (restrictionUnderlying g a M).hom.hom.app U x) := by
  let N := (SuccessiveDerivedQuotient.restriction a).obj M
  let A := (underlying S).obj M
  let B := (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj R
  let e := (g.inverse R).moduleUnderlying.app N
  let er := (g.inverse R).ringUnderlying
  let p := imagePair B A U (er.inv.hom.app U t) (e.hom.hom.app U x)
  let b : B ⨯ A ⟶ (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj S :=
    prod.fst ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map a
  have hR := (g.inverse R).moduleSMul N (B ⨯ A) prod.fst prod.snd (smulMap N)
    (fun _ _ ↦ rfl) U p
  have hS := (g.inverse S).moduleSMul M (B ⨯ A) b prod.snd (smulMap N)
    (fun _ _ ↦ rfl) U p
  have ht : er.hom.hom.app U ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p) = t := by
    rw [imagePair_fst]
    exact congrArg (fun k ↦ k.hom.app U t) er.inv_hom_id
  have hx : e.inv.hom.app U ((uInv.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p) = x := by
    rw [imagePair_snd]
    exact congrArg (fun k ↦ k.hom.app U x) e.hom_inv_id
  dsimp only [id] at hR hS
  change e.inv.hom.app U ((uInv.map (smulMap N)).hom.app U p) =
    (show (g.rings.obj R).obj.obj U from
      er.hom.hom.app U ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) •
      (show ((g.inverse R).modules.obj N).val.obj U from
        e.inv.hom.app U ((uInv.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p)) at hR
  have hR' := hR.trans (congrArg₂ (· • ·) ht hx)
  change ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
      ((uInv.map (smulMap N)).hom.app U p) =
    (show (g.rings.obj S).obj.obj U from
      (g.inverse S).ringUnderlying.hom.hom.app U ((uInv.map b).hom.app U p)) •
      (show ((g.inverse S).modules.obj M).val.obj U from
        ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
          ((uInv.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p)) at hS
  have hb : ((g.inverse S).ringUnderlying.hom).hom.app U
      ((uInv.map b).hom.app U p) = (g.rings.map a).hom.app U t := by
    have h := congrArg (fun k ↦ k.hom.app U
      ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p))
      (g.rings_naturality a)
    change ((g.inverse S).ringUnderlying.hom).hom.app U
        ((uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map a)).hom.app U
          ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) =
      (g.rings.map a).hom.app U
        (er.hom.hom.app U ((uInv.map (prod.fst : B ⨯ A ⟶ B)).hom.app U p)) at h
    rw [ht] at h
    simpa only [b, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply] using h
  have hp : (uInv.map (prod.snd : B ⨯ A ⟶ A)).hom.app U p =
      e.hom.hom.app U x := imagePair_snd B A U _ _
  have hS' := hS.trans (congrArg₂ (· • ·) hb
    (congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z) hp))
  let f : ((g.inverse R).modules.obj N).val.obj U →
      ((g.inverse S).modules.obj M).val.obj U := fun z ↦
    ((g.inverse S).moduleUnderlying.inv.app M).hom.app U (e.hom.hom.app U z)
  have h := congrArg f hR'
  have hc : f (e.inv.hom.app U ((uInv.map (smulMap N)).hom.app U p)) =
      ((g.inverse S).moduleUnderlying.inv.app M).hom.app U
        ((uInv.map (smulMap N)).hom.app U p) :=
    congrArg (fun z ↦ ((g.inverse S).moduleUnderlying.inv.app M).hom.app U z)
      (congrArg (fun k ↦ k.hom.app U ((uInv.map (smulMap N)).hom.app U p)) e.inv_hom_id)
  change f (t • x) = (g.rings.map a).hom.app U t • f x
  exact h.symm.trans (hc.trans hS')

private def restrictionMap [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) :
    (g.inverse R).modules.obj ((SuccessiveDerivedQuotient.restriction a).obj M) ⟶
      (SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj
        ((g.inverse S).modules.obj M) :=
  SheafOfModules.linearLift (restrictionUnderlying g a M).hom
    (restrictionUnderlying_add g a M) (restrictionUnderlying_smul g a M)

private theorem restrictionMap_isIso [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) :
    IsIso (restrictionMap g a M) := by
  have : IsIso ((underlying (g.rings.obj R)).map (restrictionMap g a M)) := by
    change IsIso (restrictionUnderlying g a M).hom
    infer_instance
  exact isIso_of_reflects_iso (restrictionMap g a M) (underlying (g.rings.obj R))

private def restrictionIso [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    SuccessiveDerivedQuotient.restriction a ⋙ (g.inverse R).modules ≅
      (g.inverse S).modules ⋙ SuccessiveDerivedQuotient.restriction (g.rings.map a) := by
  have := restrictionMap_isIso g a
  refine NatIso.ofComponents (fun M ↦ asIso (restrictionMap g a M)) ?_
  intro M N f
  apply (underlying (g.rings.obj R)).map_injective
  change (underlying (g.rings.obj R)).map
      ((g.inverse R).modules.map ((SuccessiveDerivedQuotient.restriction a).map f)) ≫
        (restrictionUnderlying g a N).hom =
      (restrictionUnderlying g a M).hom ≫
        (underlying (g.rings.obj S)).map ((g.inverse S).modules.map f)
  have hR := (g.inverse R).moduleUnderlying.hom.naturality
    ((SuccessiveDerivedQuotient.restriction a).map f)
  have hS := (g.inverse S).moduleUnderlying.inv.naturality f
  dsimp only [Functor.comp_map] at hR hS
  dsimp only [restrictionUnderlying, Iso.trans_hom, Iso.symm_hom]
  erw [← Category.assoc, hR, Category.assoc, hS]
  rfl

private theorem restrictionIso_hom_underlying [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J S) :
    (underlying (g.rings.obj R)).map ((restrictionIso g a).hom.app M) =
      (g.inverse R).moduleUnderlying.hom.app
          ((SuccessiveDerivedQuotient.restriction a).obj M) ≫
        (g.inverse S).moduleUnderlying.inv.app M := rfl

attribute [local irreducible] restrictionMap restrictionIso

private theorem adjunction_underlying
    (R : Sheaf J CommRingCat.{r}) (M : Mod J R) (N : Mod K (g.rings.obj R))
    (f : (g.inverse R).modules.obj M ⟶ N) :
    (underlying R).map ((g.ordinaryAdjunction R).homEquiv M N f) ≫
        (g.pushUnderlying R).hom.app N =
      adj.homEquiv _ _ ((g.inverse R).moduleUnderlying.inv.app M ≫
        (underlying (g.rings.obj R)).map f) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := (g.pushUnderlying R).hom.naturality f
  change (underlying R).map ((g.push R).map f) ≫
      (g.pushUnderlying R).hom.app N =
    (g.pushUnderlying R).hom.app ((g.inverse R).modules.obj M) ≫
      uPush.map ((underlying (g.rings.obj R)).map f) at hn
  rw [Category.assoc, hn]
  change _ = adj.unit.app ((underlying R).obj M) ≫
    uPush.map ((g.inverse R).moduleUnderlying.inv.app M ≫
      (underlying (g.rings.obj R)).map f)
  rw [← g.unit_underlying R M, Functor.map_comp]
  simp only [Category.assoc, ← uPush.map_comp, Iso.hom_inv_id_app_assoc]

private def pushRestriction [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    g.push S ⋙ SuccessiveDerivedQuotient.restriction a ⟶
      SuccessiveDerivedQuotient.restriction (g.rings.map a) ⋙ g.push R :=
  (mateEquiv (g.ordinaryAdjunction S) (g.ordinaryAdjunction R)
    (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom))

private theorem pushRestriction_underlying [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (N : Mod K (g.rings.obj S)) :
    (underlying R).map ((pushRestriction g a).app N) ≫
        (g.pushUnderlying R).hom.app
          ((SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj N) =
      (g.pushUnderlying S).hom.app N := by
  let f := (restrictionIso g a).hom.app ((g.push S).obj N) ≫
    (SuccessiveDerivedQuotient.restriction (g.rings.map a)).map
      ((g.ordinaryAdjunction S).counit.app N)
  have hm : (g.ordinaryAdjunction R).homEquiv _ _ f =
      (pushRestriction g a).app N := by
    apply ((g.ordinaryAdjunction R).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit (g.ordinaryAdjunction S) (g.ordinaryAdjunction R)
      (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom) N).symm
  rw [← hm]
  erw [adjunction_underlying g]
  have hf : (g.inverse R).moduleUnderlying.inv.app
        ((SuccessiveDerivedQuotient.restriction a).obj ((g.push S).obj N)) ≫
        (underlying (g.rings.obj R)).map f =
      (g.inverse S).moduleUnderlying.inv.app ((g.push S).obj N) ≫
        (underlying (g.rings.obj S)).map ((g.ordinaryAdjunction S).counit.app N) := by
    dsimp only [f]
    rw [Functor.map_comp, underlying_restriction_map, restrictionIso_hom_underlying]
    erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  refine (congrArg (adj.homEquiv _ _) hf).trans ?_
  refine (adjunction_underlying g S ((g.push S).obj N) N
    ((g.ordinaryAdjunction S).counit.app N)).symm.trans ?_
  have hc : (g.ordinaryAdjunction S).homEquiv ((g.push S).obj N) N
      ((g.ordinaryAdjunction S).counit.app N) = 𝟙 _ := by
    apply ((g.ordinaryAdjunction S).homEquiv _ N).symm.injective
    rw [Equiv.symm_apply_apply]
    exact (Adjunction.homEquiv_symm_id (g.ordinaryAdjunction S) N).symm
  rw [hc, CategoryTheory.Functor.map_id, Category.id_comp]

private def pushRestrictionIso [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    g.push S ⋙ SuccessiveDerivedQuotient.restriction a ≅
      SuccessiveDerivedQuotient.restriction (g.rings.map a) ⋙ g.push R := by
  have h (N : Mod K (g.rings.obj S)) : IsIso ((pushRestriction g a).app N) := by
    have he : (underlying R).map ((pushRestriction g a).app N) =
        (g.pushUnderlying S).hom.app N ≫
          (g.pushUnderlying R).inv.app
            ((SuccessiveDerivedQuotient.restriction (g.rings.map a)).obj N) := by
      apply (cancel_mono ((g.pushUnderlying R).hom.app _)).1
      rw [pushRestriction_underlying, Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    have : IsIso ((underlying R).map ((pushRestriction g a).app N)) := by
      rw [he]
      infer_instance
    exact isIso_of_reflects_iso _ (underlying R)
  letI : ∀ N, IsIso ((pushRestriction g a).app N) := h
  haveI := NatIso.isIso_of_isIso_app (pushRestriction g a)
  exact asIso (pushRestriction g a)

private def ordinaryBackward [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    (g.inverse R).modules ⋙ (pX (g.rings.map a)).ordinary ⟶
      (pY a).ordinary ⋙ (g.inverse S).modules :=
  ((mateEquiv (nY.ordinaryAdjunction a) (nX.ordinaryAdjunction (g.rings.map a))).symm
    (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom))

private theorem ordinaryBackward_isIso [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    IsIso (ordinaryBackward g nY nX a) := by
  have he : conjugateEquiv
      ((nY.ordinaryAdjunction a).comp (g.ordinaryAdjunction S))
      ((g.ordinaryAdjunction R).comp (nX.ordinaryAdjunction (g.rings.map a)))
      (ordinaryBackward g nY nX a) = pushRestriction g a := by
    let β := (mateEquiv (nY.ordinaryAdjunction a)
      (nX.ordinaryAdjunction (g.rings.map a))).symm
        (TwoSquare.mk _ _ _ _ (restrictionIso g a).hom)
    have h := iterated_mateEquiv_conjugateEquiv
      (nY.ordinaryAdjunction a) (nX.ordinaryAdjunction (g.rings.map a))
      (g.ordinaryAdjunction R) (g.ordinaryAdjunction S) β
    simpa only [β, ordinaryBackward, pushRestriction, Equiv.apply_symm_apply] using h.symm
  have : IsIso (pushRestriction g a) := by
    change IsIso (pushRestrictionIso g a).hom
    infer_instance
  have : IsIso (conjugateEquiv
      ((nY.ordinaryAdjunction a).comp (g.ordinaryAdjunction S))
      ((g.ordinaryAdjunction R).comp (nX.ordinaryAdjunction (g.rings.map a)))
      (ordinaryBackward g nY nX a)) := by rw [he]; infer_instance
  exact conjugateEquiv_of_iso
    ((nY.ordinaryAdjunction a).comp (g.ordinaryAdjunction S))
    ((g.ordinaryAdjunction R).comp (nX.ordinaryAdjunction (g.rings.map a)))
    (ordinaryBackward g nY nX a)

private def ordinaryComparison [PreservesFiniteLimits uInv]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    (pY a).ordinary ⋙ (g.inverse S).modules ≅
      (g.inverse R).modules ⋙ (pX (g.rings.map a)).ordinary := by
  have := ordinaryBackward_isIso g nY nX a
  exact (asIso (ordinaryBackward g nY nX a)).symm


end SheafOfModules.RingedCoefficientProjection

end
