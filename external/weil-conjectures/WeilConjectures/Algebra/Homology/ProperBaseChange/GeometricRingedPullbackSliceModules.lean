/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
public import WeilConjectures.Algebra.Homology.ProperBaseChange.OrdinaryRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRestrictionOrdinaryComparisons
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementSiteDescent
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Ordinary module pullback comparison on specified slices

The geometric morphism and its structural-map equation are inputs to this step.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open MonoidalCategory
namespace SheafOfModules

section SliceHelpers
variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {T : GrothendieckTopology E}

private noncomputable def sliceComposite
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (N : Sheaf K (Type u) ⥤ Sheaf T (Type u))
    {B : Sheaf J CommRingCat.{u}} {BI : Sheaf K CommRingCat.{u}}
    {BII : Sheaf T CommRingCat.{u}}
    (F : AlgebraicInverseImage L B BI)
    (G : AlgebraicInverseImage N BI BII) :
    AlgebraicInverseImage (L ⋙ N) B BII where
  ringUnderlying := N.mapIso F.ringUnderlying ≪≫ G.ringUnderlying
  ringAdd := by
    intro S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringAdd (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.ringUnderlying.hom) (L.map t ≫ F.ringUnderlying.hom)
      (F.ringAdd S a b t h) V x
  ringMul := by
    intro S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringMul (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.ringUnderlying.hom) (L.map t ≫ F.ringUnderlying.hom)
      (F.ringMul S a b t h) V x
  ringZero := by
    intro S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringZero (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (F.ringZero S a h) V x
  ringOne := by
    intro S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringOne (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (F.ringOne S a h) V x
  modules := F.modules ⋙ G.modules
  moduleUnderlying := Functor.isoWhiskerLeft F.modules G.moduleUnderlying ≪≫
    Functor.isoWhiskerRight F.moduleUnderlying N
  moduleAdd := by
    intro M S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleAdd (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.moduleUnderlying.inv.app M)
      (L.map b ≫ F.moduleUnderlying.inv.app M)
      (L.map t ≫ F.moduleUnderlying.inv.app M) (F.moduleAdd M S a b t h) V x
  moduleZero := by
    intro M S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleZero (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.moduleUnderlying.inv.app M) (F.moduleZero M S a h) V x
  moduleSMul := by
    intro M S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleSMul (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.moduleUnderlying.inv.app M)
      (L.map t ≫ F.moduleUnderlying.inv.app M) (F.moduleSMul M S a b t h) V x

private noncomputable def sliceRestriction (R : Sheaf J CommRingCat.{u})
    (B : Sheaf J (Type u)) :
    AlgebraicInverseImage (elementSheafPullback B) R (presentationElementRing R B) where
  ringUnderlying := Iso.refl _
  modules := elementModulePullback (localCoefficientRings R) B
  moduleUnderlying := Iso.refl _
  ringAdd := by intro Z a b t h V v; exact h _ v
  ringMul := by intro Z a b t h V v; exact h _ v
  ringZero := by intro Z a h V v; exact h _ v
  ringOne := by intro Z a h V v; exact h _ v
  moduleAdd := by intro M Z a b t h V v; exact h _ v
  moduleZero := by intro M Z a h V v; exact h _ v
  moduleSMul := by intro M Z a b t h V v; exact h _ v

private theorem sliceNat
    {L L' : Sheaf J (Type u) ⥤ Sheaf K (Type u)} (e : L ⟶ L')
    {X Y : Sheaf J (Type u)} (q : X ⟶ Y) (V : Dᵒᵖ) (v : (L.obj X).obj.obj V) :
    (e.app Y).hom.app V ((L.map q).hom.app V v) =
      (L'.map q).hom.app V ((e.app X).hom.app V v) :=
  congrArg (fun k ↦ k.hom.app V v) (e.naturality q)

-- The graph equations compare several composed underlying-sheaf functors.
private noncomputable def sliceTransport
    {L L' : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : L ≅ L') (I : AlgebraicInverseImage L' R S) : AlgebraicInverseImage L R S where
  ringUnderlying := e.app _ ≪≫ I.ringUnderlying
  modules := I.modules
  moduleUnderlying := I.moduleUnderlying ≪≫
    Functor.isoWhiskerLeft (toSheaf (localCoefficientRings R) ⋙
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) e.symm
  ringAdd := by
    intro Z a b t h V v
    simpa only [Iso.trans_hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply, sliceNat] using
      I.ringAdd Z a b t h V ((e.hom.app Z).hom.app V v)
  ringMul := by
    intro Z a b t h V v
    simpa only [Iso.trans_hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply, sliceNat] using
      I.ringMul Z a b t h V ((e.hom.app Z).hom.app V v)
  ringZero := by
    intro Z a h V v
    simpa only [Iso.trans_hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply, sliceNat] using
      I.ringZero Z a h V ((e.hom.app Z).hom.app V v)
  ringOne := by
    intro Z a h V v
    simpa only [Iso.trans_hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, types_comp_apply, sliceNat] using
      I.ringOne Z a h V ((e.hom.app Z).hom.app V v)
  moduleAdd := by
    intro M Z a b t h V v
    change (I.moduleUnderlying.inv.app M).hom.app V
      ((e.hom.app _).hom.app V ((L.map t).hom.app V v)) =
        (show (I.modules.obj M).val.obj V from
          (I.moduleUnderlying.inv.app M).hom.app V
            ((e.hom.app _).hom.app V ((L.map a).hom.app V v))) +
        (show (I.modules.obj M).val.obj V from
          (I.moduleUnderlying.inv.app M).hom.app V
            ((e.hom.app _).hom.app V ((L.map b).hom.app V v)))
    simp only [sliceNat e.hom t V v, sliceNat e.hom a V v, sliceNat e.hom b V v]
    exact I.moduleAdd M Z a b t h V ((e.hom.app Z).hom.app V v)

  moduleZero := by
    intro M Z a h V v
    change (I.moduleUnderlying.inv.app M).hom.app V
      ((e.hom.app _).hom.app V ((L.map a).hom.app V v)) =
        (0 : (I.modules.obj M).val.obj V)
    simp only [sliceNat e.hom a V v]
    exact I.moduleZero M Z a h V ((e.hom.app Z).hom.app V v)

  moduleSMul := by
    intro M Z a b t h V v
    change (I.moduleUnderlying.inv.app M).hom.app V
      ((e.hom.app _).hom.app V ((L.map t).hom.app V v)) =
        (show S.obj.obj V from
          I.ringUnderlying.hom.hom.app V ((e.hom.app _).hom.app V ((L.map a).hom.app V v))) •
        (show (I.modules.obj M).val.obj V from
          (I.moduleUnderlying.inv.app M).hom.app V
            ((e.hom.app _).hom.app V ((L.map b).hom.app V v)))
    simp only [sliceNat e.hom t V v, sliceNat e.hom a V v, sliceNat e.hom b V v]
    exact I.moduleSMul M Z a b t h V ((e.hom.app Z).hom.app V v)

private theorem sliceComposite_moduleUnderlying
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (N : Sheaf K (Type u) ⥤ Sheaf T (Type u))
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    {U : Sheaf T CommRingCat.{u}}
    (F : AlgebraicInverseImage L R S) (G : AlgebraicInverseImage N S U) :
    (sliceComposite L N F G).moduleUnderlying =
      Functor.isoWhiskerLeft F.modules G.moduleUnderlying ≪≫
        Functor.isoWhiskerRight F.moduleUnderlying N := rfl

private theorem sliceRestriction_moduleUnderlying
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf J (Type u)) :
    (sliceRestriction R B).moduleUnderlying = Iso.refl _ := rfl

private theorem sliceTransport_moduleUnderlying
    {L L' : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : L ≅ L') (I : AlgebraicInverseImage L' R S) :
    (sliceTransport e I).moduleUnderlying = I.moduleUnderlying ≪≫
      Functor.isoWhiskerLeft (toSheaf (localCoefficientRings R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) e.symm := rfl

private theorem sliceUnderlyingComparison
    (RY : Sheaf K CommRingCat.{u}) (RI : Sheaf J CommRingCat.{u})
    (A : Sheaf K (Type u)) (B : Sheaf J (Type u))
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (LA : Sheaf (elementTopology A) (Type u) ⥤ Sheaf (elementTopology B) (Type u))
    {RIA : Sheaf (elementTopology B) CommRingCat.{u}}
    (IA : AlgebraicInverseImage LA (presentationElementRing RY A) RIA)
    (I : AlgebraicInverseImage L RY RI)
    (a : elementSheafPullback A ⋙ LA ≅ L ⋙ elementSheafPullback B)
    (M : ringedSiteModules.{u} (localCoefficientRings RY)) :
    (sliceComposite (elementSheafPullback A) LA
        (sliceRestriction RY A) IA).moduleUnderlying.hom.app M ≫
      (sliceTransport a (sliceComposite L (elementSheafPullback B)
        I (sliceRestriction RI B))).moduleUnderlying.inv.app M =
      IA.moduleUnderlying.hom.app ((elementModulePullback (localCoefficientRings RY) A).obj M) ≫
        a.hom.app ((toSheaf (localCoefficientRings RY) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
        (elementSheafPullback B).map (I.moduleUnderlying.inv.app M) := by
  simp only [sliceComposite_moduleUnderlying, sliceRestriction_moduleUnderlying,
    sliceTransport_moduleUnderlying, Iso.trans_hom, Iso.trans_inv, Iso.refl_hom, Iso.refl_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.assoc]
  change IA.moduleUnderlying.hom.app
      ((elementModulePullback (localCoefficientRings RY) A).obj M) ≫
    𝟙 _ ≫ a.hom.app ((toSheaf (localCoefficientRings RY) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
    (elementSheafPullback B).map (I.moduleUnderlying.inv.app M) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

-- The graph equations compare several composed underlying-sheaf functors.
private noncomputable def sliceScalarSection
    {R₀ R₁ S : Sheaf J CommRingCat.{u}} (d : R₀ ≅ R₁)
    (c₀ : R₀ ⟶ S) (c₁ : R₁ ⟶ S) (hc : d.hom ≫ c₁ = c₀)
    (M : ringedSiteModules.{u} (localCoefficientRings R₀))
    (N : ringedSiteModules.{u} (localCoefficientRings R₁))
    (b : M ≅ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map d.hom)).obj N)
    (V : Cᵒᵖ) :
    (changeOfRingsPresheaf.{u, u, u} c₀ M).obj V ≅
      (changeOfRingsPresheaf.{u, u, u} c₁ N).obj V := by
  let e := ((sheafToPresheaf J CommRingCat).mapIso d).app V
  let q : R₀.obj.obj V ≃+* R₁.obj.obj V := e.commRingCatIsoToRingEquiv
  let σ := q.toRingHom
  let σ' := q.symm.toRingHom
  letI : Module (R₀.obj.obj V) (S.obj.obj V) :=
    Module.compHom (S.obj.obj V) (c₀.hom.app V).hom
  letI : Module (R₁.obj.obj V) (S.obj.obj V) :=
    Module.compHom (S.obj.obj V) (c₁.hom.app V).hom
  letI : RingHomInvPair σ σ' := RingHomInvPair.of_ringEquiv q
  letI : RingHomInvPair σ' σ := RingHomInvPair.of_ringEquiv_symm q
  let f : S.obj.obj V ≃ₛₗ[σ] S.obj.obj V :=
    { Equiv.refl _ with
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r t
        change c₀.hom.app V r * t = c₁.hom.app V (d.hom.hom.app V r) * t
        exact congrArg (fun z : S.obj.obj V ↦ z * t)
          (ConcreteCategory.congr_hom (congrArg (fun h ↦ h.hom.app V) hc) r).symm }
  let g : M.val.obj V ≃ₛₗ[σ] N.val.obj V :=
    { toFun := fun m ↦ @id (N.val.obj V) (b.hom.val.app V m)
      invFun := fun m ↦ @id (M.val.obj V) (b.inv.val.app V m)
      left_inv := fun x ↦ congrArg (fun h ↦ h.val.app V x) b.hom_inv_id
      right_inv := fun x ↦ congrArg (fun h ↦ h.val.app V x) b.inv_hom_id
      map_add' := (b.hom.val.app V).hom.map_add
      map_smul' := (b.hom.val.app V).hom.map_smul }
  let t := TensorProduct.congr f g
  let t' : (changeOfRingsPresheaf.{u, u, u} c₀ M).obj V ≃ₗ[S.obj.obj V]
      (changeOfRingsPresheaf.{u, u, u} c₁ N).obj V :=
    { t.toAddEquiv with
      map_smul' := by
        intro r z
        change t (r • z) = r • t z
        induction z using TensorProduct.inductionOn with
        | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
        | tmul s m =>
          change t (r • (s ⊗ₜ[R₀.obj.obj V, (c₀.hom.app V).hom] m)) =
            r • t (s ⊗ₜ[R₀.obj.obj V, (c₀.hom.app V).hom] m)
          rw [ModuleCat.ExtendScalars.smul_tmul, TensorProduct.congr_tmul]
          change (r * (@id (S.obj.obj V) s)) ⊗ₜ[R₁.obj.obj V, (c₁.hom.app V).hom]
            (@id (N.val.obj V) (b.hom.val.app V m)) =
              r • ((@id (S.obj.obj V) s) ⊗ₜ[R₁.obj.obj V, (c₁.hom.app V).hom]
                (@id (N.val.obj V) (b.hom.val.app V m)))
          exact (ModuleCat.ExtendScalars.smul_tmul _ r (@id (S.obj.obj V) s) _).symm }
  exact t'.toModuleIso

private theorem sliceScalarSection_tmul
    {R₀ R₁ S : Sheaf J CommRingCat.{u}} (d : R₀ ≅ R₁)
    (c₀ : R₀ ⟶ S) (c₁ : R₁ ⟶ S) (hc : d.hom ≫ c₁ = c₀)
    (M : ringedSiteModules.{u} (localCoefficientRings R₀))
    (N : ringedSiteModules.{u} (localCoefficientRings R₁))
    (b : M ≅ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map d.hom)).obj N)
    (V : Cᵒᵖ) (r : S.obj.obj V) (m : M.val.obj V) :
    (sliceScalarSection d c₀ c₁ hc M N b V).hom
      (r ⊗ₜ[R₀.obj.obj V, (c₀.hom.app V).hom] m) =
        r ⊗ₜ[R₁.obj.obj V, (c₁.hom.app V).hom]
          (@id (N.val.obj V) (b.hom.val.app V m)) := rfl

private theorem sliceChangeMap_tmul {R S : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) (M : ringedSiteModules.{u} (localCoefficientRings R))
    {V W : Cᵒᵖ} (v : V ⟶ W) (r : S.obj.obj V) (m : M.val.obj V) :
    changeOfRingsMap c M v (r ⊗ₜ[R.obj.obj V, (c.hom.app V).hom] m) =
      S.obj.map v r ⊗ₜ[R.obj.obj W, (c.hom.app W).hom]
        PresheafOfModulesOfCommRing.map (R := R.obj) M.val v m :=
  Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} c M v) r m

private noncomputable def sliceScalarRaw
    {R₀ R₁ S : Sheaf J CommRingCat.{u}} (d : R₀ ≅ R₁)
    (c₀ : R₀ ⟶ S) (c₁ : R₁ ⟶ S) (hc : d.hom ≫ c₁ = c₀)
    (M : ringedSiteModules.{u} (localCoefficientRings R₀))
    (N : ringedSiteModules.{u} (localCoefficientRings R₁))
    (b : M ≅ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map d.hom)).obj N) :
    changeOfRingsPresheaf.{u, u, u} c₀ M ≅ changeOfRingsPresheaf.{u, u, u} c₁ N := by
  refine PresheafOfModules.isoMk (sliceScalarSection d c₀ c₁ hc M N b) ?_
  intro V W v
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (sliceScalarSection d c₀ c₁ hc M N b W).hom
    (changeOfRingsMap c₀ M v ((1 : S.obj.obj V) ⊗ₜ[R₀.obj.obj V, (c₀.hom.app V).hom] m)) =
      changeOfRingsMap c₁ N v
        ((sliceScalarSection d c₀ c₁ hc M N b V).hom
          ((1 : S.obj.obj V) ⊗ₜ[R₀.obj.obj V, (c₀.hom.app V).hom] m))
  rw [sliceChangeMap_tmul, sliceScalarSection_tmul, sliceScalarSection_tmul,
    sliceChangeMap_tmul]
  congr 1
  exact PresheafOfModules.naturality_apply b.hom.val v m

private theorem sliceSheafification
    (R : Sheaf J RingCat.{u}) (B : Sheaf J (Type u)) (P : PresheafOfModules.{u} R.obj) :
    ∃ e : (PresheafOfModules.sheafification.{u, u, u, u} (𝟙 (elementRing R B).obj)).obj
        ((PresheafOfModules.pushforward₀ (elementProjection B) R.obj).obj P) ≅
      (elementModulePullback R B).obj
        ((PresheafOfModules.sheafification.{u, u, u, u} (𝟙 R.obj)).obj P),
      ∀ (V : B.obj.Elementsᵒᵖᵒᵖ) (z : P.obj ((elementProjection B).op.obj V)),
        e.hom.val.app V
          (((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
            (𝟙 (elementRing R B).obj)).unit.app
              ((PresheafOfModules.pushforward₀ (elementProjection B) R.obj).obj P)).app V z) =
          ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u} (𝟙 R.obj)).unit.app P).app
            ((elementProjection B).op.obj V) z := by
  classical
  let F := elementProjection B
  let : F.IsCocontinuous (elementTopology B) J := (element_site_descent B).2.1
  let S := PresheafOfModules.sheafification.{u, u, u, u} (𝟙 (elementRing R B).obj)
  let P' := (PresheafOfModules.pushforward₀ F R.obj).obj P
  let H := (elementModulePullback R B).obj
    ((PresheafOfModules.sheafification.{u, u, u, u} (𝟙 R.obj)).obj P)
  let k : P' ⟶ H.val := (PresheafOfModules.pushforward₀ F R.obj).map
    ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u} (𝟙 R.obj)).unit.app P)
  let h : S.obj P' ⟶ H :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (elementRing R B).obj)).symm k
  have hh : (toSheaf (elementRing R B)).map h =
      (F.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u}
        (elementTopology B) J).hom.app P.presheaf := by
    dsimp only [h]
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      (elementTopology B) AddCommGrpCat.{u}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact (F.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat.{u}
      (elementTopology B) J P.presheaf).symm
  have : IsIso h := by
    have : IsIso ((toSheaf (elementRing R B)).map h) := by rw [hh]; infer_instance
    exact isIso_of_reflects_iso h (toSheaf (elementRing R B))
  refine ⟨asIso h, ?_⟩
  intro V z
  have hu := (PresheafOfModules.sheafificationHomEquiv.{u, u, u, u}
    (P := P') (F := H) (𝟙 (elementRing R B).obj)).apply_symm_apply k
  exact congrArg (fun k ↦ k.app V z) hu

private noncomputable def sliceRingMap {R S : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) (B : Sheaf J (Type u)) :
    presentationElementRing R B ⟶ presentationElementRing S B :=
  ⟨Functor.whiskerLeft (elementProjection B).op c.hom⟩

private noncomputable def sliceTensorRaw {R S : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) (B : Sheaf J (Type u))
    (M : ringedSiteModules.{u} (localCoefficientRings R)) :
    changeOfRingsPresheaf.{u, u, u} (sliceRingMap c B)
        ((elementModulePullback.{u, u} (localCoefficientRings R) B).obj M) ≅
      (PresheafOfModules.pushforward₀ (elementProjection B) (localCoefficientRings S).obj).obj
        (changeOfRingsPresheaf.{u, u, u} c M) := by
  refine PresheafOfModules.isoMk (fun V ↦ (LinearEquiv.refl _ _).toModuleIso) ?_
  intro V W v
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change changeOfRingsMap (sliceRingMap c B)
    ((elementModulePullback (localCoefficientRings R) B).obj M) v
      ((1 : S.obj.obj ((elementProjection B).op.obj V)) ⊗ₜ[
        _, ((sliceRingMap c B).hom.app V).hom] m) =
        changeOfRingsMap c M ((elementProjection B).op.map v)
          ((1 : S.obj.obj ((elementProjection B).op.obj V)) ⊗ₜ[
            _, (c.hom.app ((elementProjection B).op.obj V)).hom] m)
  rw [sliceChangeMap_tmul, sliceChangeMap_tmul]
  rfl

-- The two graph presentations are compared on preserved products of section sheaves.
@[irreducible] private noncomputable def sliceRingHom
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{u}} {S₀ S₁ : Sheaf K CommRingCat.{u}}
    (P : AlgebraicInverseImage L R S₀) (Q : AlgebraicInverseImage L R S₁) : S₀ ⟶ S₁ := by
  let α := P.ringUnderlying.inv ≫ Q.ringUnderlying.hom
  let X := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
  let opAdd : X ⊗ X ⟶ X :=
    ⟨{ app := fun U ↦ ↾(fun z ↦ @Add.add (R.obj.obj U) inferInstance z.1 z.2)
       naturality := by intro U V g; ext z; exact ((R.obj.map g).hom.map_add _ _).symm }⟩
  let opMul : X ⊗ X ⟶ X :=
    ⟨{ app := fun U ↦ ↾(fun z ↦ @Mul.mul (R.obj.obj U) inferInstance z.1 z.2)
       naturality := by intro U V g; ext z; exact ((R.obj.map g).hom.map_mul _ _).symm }⟩
  let h (V : Dᵒᵖ) (x y : S₀.obj.obj V) :=
    CategoryTheory.FlatRingedDiagramInput.pairPreimage L X X V
      (P.ringUnderlying.inv.hom.app V x) (P.ringUnderlying.inv.hom.app V y)
  have hf (V : Dᵒᵖ) (x y : S₀.obj.obj V) :
      (L.map (CartesianMonoidalCategory.fst X X)).hom.app V (h V x y) =
        P.ringUnderlying.inv.hom.app V x :=
    CategoryTheory.FlatRingedDiagramInput.pairPreimage_fst L X X V
      (P.ringUnderlying.inv.hom.app V x) (P.ringUnderlying.inv.hom.app V y)
  have hs (V : Dᵒᵖ) (x y : S₀.obj.obj V) :
      (L.map (CartesianMonoidalCategory.snd X X)).hom.app V (h V x y) =
        P.ringUnderlying.inv.hom.app V y :=
    CategoryTheory.FlatRingedDiagramInput.pairPreimage_snd L X X V
      (P.ringUnderlying.inv.hom.app V x) (P.ringUnderlying.inv.hom.app V y)
  have hi (V : Dᵒᵖ) (r : S₀.obj.obj V) :
      P.ringUnderlying.hom.hom.app V (P.ringUnderlying.inv.hom.app V r) = r :=
    congrArg (fun k ↦ k.hom.app V r) P.ringUnderlying.inv_hom_id
  have ha (V : Dᵒᵖ) (x y : S₀.obj.obj V) :
      α.hom.app V (x + y) =
        (show S₁.obj.obj V from α.hom.app V x) +
          (show S₁.obj.obj V from α.hom.app V y) := by
    have hp := P.ringAdd (X ⊗ X) (CartesianMonoidalCategory.fst X X)
      (CartesianMonoidalCategory.snd X X) opAdd (fun _ _ ↦ rfl) V (h V x y)
    dsimp only [id] at hp
    rw [hf, hs, hi, hi] at hp
    have hq := Q.ringAdd (X ⊗ X) (CartesianMonoidalCategory.fst X X)
      (CartesianMonoidalCategory.snd X X) opAdd (fun _ _ ↦ rfl) V (h V x y)
    dsimp only [id] at hq
    rw [hf, hs] at hq
    change Q.ringUnderlying.hom.hom.app V
      (P.ringUnderlying.inv.hom.app V (x + y)) = _
    rw [← hp]
    have hh := congrArg (fun k ↦ k.hom.app V ((L.map opAdd).hom.app V (h V x y)))
      P.ringUnderlying.hom_inv_id
    change P.ringUnderlying.inv.hom.app V
      (P.ringUnderlying.hom.hom.app V ((L.map opAdd).hom.app V (h V x y))) = _ at hh
    rw [hh]
    exact hq
  have hm (V : Dᵒᵖ) (x y : S₀.obj.obj V) :
      α.hom.app V (x * y) =
        (show S₁.obj.obj V from α.hom.app V x) *
          (show S₁.obj.obj V from α.hom.app V y) := by
    have hp := P.ringMul (X ⊗ X) (CartesianMonoidalCategory.fst X X)
      (CartesianMonoidalCategory.snd X X) opMul (fun _ _ ↦ rfl) V (h V x y)
    dsimp only [id] at hp
    rw [hf, hs, hi, hi] at hp
    have hq := Q.ringMul (X ⊗ X) (CartesianMonoidalCategory.fst X X)
      (CartesianMonoidalCategory.snd X X) opMul (fun _ _ ↦ rfl) V (h V x y)
    dsimp only [id] at hq
    rw [hf, hs] at hq
    change Q.ringUnderlying.hom.hom.app V
      (P.ringUnderlying.inv.hom.app V (x * y)) = _
    rw [← hp]
    have hh := congrArg (fun k ↦ k.hom.app V ((L.map opMul).hom.app V (h V x y)))
      P.ringUnderlying.hom_inv_id
    change P.ringUnderlying.inv.hom.app V
      (P.ringUnderlying.hom.hom.app V ((L.map opMul).hom.app V (h V x y))) = _ at hh
    rw [hh]
    exact hq
  have ho (V : Dᵒᵖ) : α.hom.app V (1 : S₀.obj.obj V) = (1 : S₁.obj.obj V) := by
    let r : X ⟶ X :=
      ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : R.obj.obj U))
         naturality := by intro U V g; ext z; exact ((R.obj.map g).hom.map_one).symm }⟩
    let z := P.ringUnderlying.inv.hom.app V (0 : S₀.obj.obj V)
    have hp := P.ringOne X r (fun _ _ ↦ rfl) V z
    dsimp only [id] at hp
    change Q.ringUnderlying.hom.hom.app V
      (P.ringUnderlying.inv.hom.app V (1 : S₀.obj.obj V)) = _
    rw [← hp]
    have hh := congrArg (fun k ↦ k.hom.app V ((L.map r).hom.app V z))
      P.ringUnderlying.hom_inv_id
    change P.ringUnderlying.inv.hom.app V
      (P.ringUnderlying.hom.hom.app V ((L.map r).hom.app V z)) = _ at hh
    rw [hh]
    exact Q.ringOne X r (fun _ _ ↦ rfl) V z
  exact ⟨
    { app := fun V ↦ CommRingCat.ofHom
        { toFun := α.hom.app V
          map_one' := ho V
          map_mul' := hm V
          map_zero' := by
            have hh := ha V 0 0
            simp only [add_zero] at hh
            exact (add_left_cancel ((add_zero _).trans hh)).symm
          map_add' := ha V }
      naturality := by
        intro V W g
        ext z
        exact ConcreteCategory.congr_hom (α.hom.naturality g) z }⟩

private theorem sliceRingHom_underlying
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{u}} {S₀ S₁ : Sheaf K CommRingCat.{u}}
    (P : AlgebraicInverseImage L R S₀) (Q : AlgebraicInverseImage L R S₁) :
    (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map (sliceRingHom P Q) =
      P.ringUnderlying.inv ≫ Q.ringUnderlying.hom := by
  unfold sliceRingHom
  rfl

private theorem sliceModuleComparison
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{u}} {S₀ S₁ : Sheaf K CommRingCat.{u}}
    (P : AlgebraicInverseImage L R S₀) (Q : AlgebraicInverseImage L R S₁)
    (d : S₀ ≅ S₁)
    (hd : P.ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map d.hom =
        Q.ringUnderlying.hom) :
    ∃ b : P.modules ≅ Q.modules ⋙
        restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map d.hom),
      ∀ M, (toSheaf (localCoefficientRings S₀) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map (b.hom.app M) =
          P.moduleUnderlying.hom.app M ≫ Q.moduleUnderlying.inv.app M := by
  classical
  let U := toSheaf (localCoefficientRings S₀) ⋙
    sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})
  let res := restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map d.hom)
  have he (M : ringedSiteModules.{u} (localCoefficientRings R)) :=
    CategoryTheory.FlatRingedDiagramInput.inverse_change_hom P Q (𝟙 R) d.hom rfl
      (by
        rw [CategoryTheory.Functor.map_id, L.map_id, eqToHom_refl,
          Category.id_comp, Category.id_comp]
        exact hd) M
  let f (M : ringedSiteModules.{u} (localCoefficientRings R)) :
      P.modules.obj M ⟶ res.obj (Q.modules.obj M) := (he M).choose
  have hf (M : ringedSiteModules.{u} (localCoefficientRings R)) :
      U.map (f M) = P.moduleUnderlying.hom.app M ≫ Q.moduleUnderlying.inv.app M := by
    have hh := (he M).choose_spec
    simp only [eqToHom_refl, Category.id_comp] at hh
    change U.map (f M) = P.moduleUnderlying.hom.app M ≫ Q.moduleUnderlying.inv.app M at hh
    exact hh
  have hi (M : ringedSiteModules.{u} (localCoefficientRings R)) : IsIso (f M) := by
    have : IsIso (U.map (f M)) := by rw [hf]; infer_instance
    exact isIso_of_reflects_iso (f M) U
  refine ⟨NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ (f M) (hi M)) ?_, hf⟩
  intro M N g
  apply U.map_injective
  change U.map (P.modules.map g ≫ f N) = U.map (f M ≫ res.map (Q.modules.map g))
  rw [Functor.map_comp, Functor.map_comp, hf, hf]
  change U.map (P.modules.map g) ≫ P.moduleUnderlying.hom.app N ≫
    Q.moduleUnderlying.inv.app N =
      (P.moduleUnderlying.hom.app M ≫ Q.moduleUnderlying.inv.app M) ≫
        U.map (res.map (Q.modules.map g))
  erw [← Category.assoc, P.moduleUnderlying.hom.naturality g, Category.assoc,
    Q.moduleUnderlying.inv.naturality g, Category.assoc]
  rfl

private noncomputable abbrev slicePure
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
    (M : ringedSiteModules.{u} (localCoefficientRings R))
    (V : Cᵒᵖ) (r : S.obj.obj V) (m : M.val.obj V) :=
  ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
    (𝟙 (localCoefficientRings S).obj)).unit.app
      (changeOfRingsPresheaf.{u, u, u} c M)).app V
        (r ⊗ₜ[R.obj.obj V, (c.hom.app V).hom] m)

private theorem slicePure_map
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
    {M N : ringedSiteModules.{u} (localCoefficientRings R)} (h : M ⟶ N)
    (V : Cᵒᵖ) (r : S.obj.obj V) (m : M.val.obj V) :
    (changeOfRingsHom.{u, u, u} c M h).val.app V (slicePure c M V r m) =
      slicePure c N V r (h.val.app V m) := by
  let p : changeOfRingsPresheaf.{u, u, u} c M ⟶
      changeOfRingsPresheaf.{u, u, u} c N :=
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (h.val.app W)
      naturality := changeOfRingsHom_naturality c M h }
  have hn := (PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
    (𝟙 (localCoefficientRings S).obj)).unit.naturality p
  have he := congrArg (fun k ↦ k.app V
    (r ⊗ₜ[R.obj.obj V, (c.hom.app V).hom] m)) hn
  change slicePure c N V r (h.val.app V m) =
    (changeOfRingsHom.{u, u, u} c M h).val.app V (slicePure c M V r m) at he
  exact he.symm

private theorem sliceScalar_ext
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
    (M : ringedSiteModules.{u} (localCoefficientRings R))
    {N : ringedSiteModules.{u} (localCoefficientRings S)}
    {f g : changeOfRings.{u, u, u} c M ⟶ N}
    (h : ∀ (V : Cᵒᵖ) (m : M.val.obj V),
      f.val.app V (slicePure c M V 1 m) = g.val.app V (slicePure c M V 1 m)) : f = g := by
  apply (PresheafOfModules.sheafificationHomEquiv.{u, u, u, u}
    (J := J) (P := changeOfRingsPresheaf.{u, u, u} c M) (F := N)
    (𝟙 (localCoefficientRings S).obj)).injective
  ext V : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact h V m

private theorem sliceTensorComparison
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S) (B : Sheaf J (Type u))
    {R₀ : Sheaf (elementTopology B) CommRingCat.{u}}
    (d : R₀ ≅ presentationElementRing R B)
    (c₀ : R₀ ⟶ presentationElementRing S B)
    (hc : d.hom ≫ sliceRingMap c B = c₀)
    (M₀ : ringedSiteModules.{u} (localCoefficientRings R₀))
    (M : ringedSiteModules.{u} (localCoefficientRings R))
    (b : M₀ ≅ (restrictScalars
        ((sheafCompose (elementTopology B) (forget₂ CommRingCat RingCat)).map d.hom)).obj
      ((elementModulePullback.{u, u} (localCoefficientRings R) B).obj M)) :
    ∃ e : changeOfRings.{u, u, u} c₀ M₀ ≅
      (elementModulePullback.{u, u} (localCoefficientRings S) B).obj
        (changeOfRings.{u, u, u} c M),
      ∀ (V : B.obj.Elementsᵒᵖᵒᵖ)
        (r : S.obj.obj ((elementProjection B).op.obj V)) (m : M₀.val.obj V),
        e.hom.val.app V (slicePure c₀ M₀ V r m) =
          slicePure c M ((elementProjection B).op.obj V) r
            (@id (M.val.obj ((elementProjection B).op.obj V)) (b.hom.val.app V m)) := by
  let q := sliceScalarRaw d c₀ (sliceRingMap c B) hc M₀
    ((elementModulePullback (localCoefficientRings R) B).obj M) b ≪≫ sliceTensorRaw c B M
  let SF := PresheafOfModules.sheafification.{u, u, u, u}
    (𝟙 (localCoefficientRings (presentationElementRing S B)).obj)
  obtain ⟨t, ht⟩ := sliceSheafification (localCoefficientRings S) B
    (changeOfRingsPresheaf.{u, u, u} c M)
  let e := SF.mapIso q ≪≫ t
  refine ⟨e, ?_⟩
  intro V r m
  have hn := (PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
    (𝟙 (localCoefficientRings (presentationElementRing S B)).obj)).unit.naturality q.hom
  have hn' := congrArg (fun k ↦ k.app V
    (r ⊗ₜ[R₀.obj.obj V, (c₀.hom.app V).hom] m)) hn
  change t.hom.val.app V ((SF.map q.hom).val.app V (slicePure c₀ M₀ V r m)) = _
  change ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
      (𝟙 (localCoefficientRings (presentationElementRing S B)).obj)).unit.app _).app V
      (q.hom.app V (r ⊗ₜ[R₀.obj.obj V, (c₀.hom.app V).hom] m)) =
        (SF.map q.hom).val.app V (slicePure c₀ M₀ V r m) at hn'
  rw [← hn']
  apply ht

private theorem sliceTensorComparisonNaturality
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S) (B : Sheaf J (Type u))
    {R₀ : Sheaf (elementTopology B) CommRingCat.{u}}
    (d : R₀ ≅ presentationElementRing R B) (c₀ : R₀ ⟶ presentationElementRing S B)
    {RY : Sheaf K CommRingCat.{u}}
    (P : ringedSiteModules.{u} (localCoefficientRings RY) ⥤
      ringedSiteModules.{u} (localCoefficientRings R₀))
    (G : ringedSiteModules.{u} (localCoefficientRings RY) ⥤
      ringedSiteModules.{u} (localCoefficientRings R))
    (b : P ⟶ (G ⋙ elementModulePullback (localCoefficientRings R) B) ⋙
      restrictScalars ((sheafCompose (elementTopology B) (forget₂ CommRingCat RingCat)).map d.hom))
    (e : ∀ M, changeOfRings.{u, u, u} c₀ (P.obj M) ≅
      (elementModulePullback (localCoefficientRings S) B).obj
        (changeOfRings.{u, u, u} c (G.obj M)))
    (he : ∀ M (V : B.obj.Elementsᵒᵖᵒᵖ)
      (r : S.obj.obj ((elementProjection B).op.obj V)) (m : (P.obj M).val.obj V),
      (e M).hom.val.app V (slicePure c₀ (P.obj M) V r m) =
        slicePure c (G.obj M) ((elementProjection B).op.obj V) r
          (@id ((G.obj M).val.obj ((elementProjection B).op.obj V)) ((b.app M).val.app V m)))
    (M N : ringedSiteModules.{u} (localCoefficientRings RY)) (h : M ⟶ N) :
    changeOfRingsHom c₀ (P.obj M) (P.map h) ≫ (e N).hom =
      (e M).hom ≫ (elementModulePullback (localCoefficientRings S) B).map
        (changeOfRingsHom c (G.obj M) (G.map h)) := by
  apply sliceScalar_ext c₀ (P.obj M)
  intro V m
  change (e N).hom.val.app V
    ((changeOfRingsHom c₀ (P.obj M) (P.map h)).val.app V
      (slicePure c₀ (P.obj M) V 1 m)) =
    (changeOfRingsHom c (G.obj M) (G.map h)).val.app ((elementProjection B).op.obj V)
      ((e M).hom.val.app V (slicePure c₀ (P.obj M) V 1 m))
  rw [slicePure_map, he, he, slicePure_map]
  congr 1
  exact congrArg (fun q ↦ q.val.app V m) (b.naturality h)

end SliceHelpers
-- Elaborating the sliced presentations unfolds several layers of functors.
/-- Ordinary module pullback commutes with localization once the sliced data are given.

Source: Stacks Project, Modules on Sites, Tags 04IF, 04IE, 03EL and 03EK
(blueprint: lem-weil-pbc-geometric-ringed-pullback-slice-modules).

Proof: Put B = f.inverse.obj A. Restrict RI and I.modules to the element site of B.
For the source restrictions, transport these objects through a and the underlying
isomorphisms of I. This defines RIA and IA: transport the ring operations and module
operations along those isomorphisms, and use naturality at each operation to verify
the generalized-section graph equations. Define ca by sectionwise restriction of c.
The underlying-map equation for ca follows from that for c and the hypothesis hr.
For every M, the source ordinary pullback is the sheafification of the presheaf
whose sections are RX tensor over RIA with IA of the restriction of M. The comparison
on its generators sends r tensor m to r tensor the image of m under the composite
IA.moduleUnderlying, a, and I.moduleUnderlying.inv. The structural-map equation hr
shows that this pairing is balanced over RIA, and the module graph equations show
additivity. The pairing is linear over the restricted RX. It therefore descends to
the presheaf tensor and then to its sheafification. Equivalently, apply the inverse
of the tensor comparison for the localization with coefficient ring RI and identity
structural map, after changing coefficients through the ring component of a.
Construct its inverse by the same recipe using the inverse underlying comparisons.
The two composites fix every local pure tensor and hence are identities by the tensor
and sheafification universal properties. For a module map h, both paths in the required
naturality square agree on local pure tensors by naturality of a and I.moduleUnderlying;
the same universal properties give the displayed equality. Evaluating the defining
pairing at the element-site object (W,b) gives exactly the final normalization equation.
This argument uses local generators before sheafification and does not assume that
sections of a tensor sheaf are globally pure tensors. -/
theorem geometric_ringed_pullback_slice_modules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u))
    (y : RingedSheafSliceAdjunctionData (localCoefficientRings RY) A)
    (x : RingedSheafSliceAdjunctionData (localCoefficientRings RX) (f.inverse.obj A))
    (fA : RingedToposMorphism
        (localCoefficientRings (presentationElementRing RX (f.inverse.obj A)))
        (localCoefficientRings (presentationElementRing RY A)))
    (slice : fA.inverse ≅ y.fibreEquivalence.functor ⋙ Over.post f.inverse ⋙
        x.fibreEquivalence.inverse)
    (a : elementSheafPullback A ⋙ fA.inverse ≅
        f.inverse ⋙ elementSheafPullback (f.inverse.obj A))
    (hr : fA.ringMap = a.hom.app
        ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj (localCoefficientRings RY)) ≫
      (elementSheafPullback (f.inverse.obj A)).map f.ringMap) :
      ∀ (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse RY RI)
        (c : RI ⟶ RX),
        I.ringUnderlying.hom ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
          f.ringMap →
        ∃ (RIA : Sheaf (elementTopology (f.inverse.obj A)) CommRingCat.{u})
          (IA : AlgebraicInverseImage fA.inverse (presentationElementRing RY A) RIA)
          (ca : RIA ⟶ presentationElementRing RX (f.inverse.obj A)),
          IA.ringUnderlying.hom ≫
              (sheafCompose (elementTopology (f.inverse.obj A))
                (CategoryTheory.forget CommRingCat.{u})).map ca = fA.ringMap ∧
          ∃ e : ∀ M : ringedSiteModules.{u} (localCoefficientRings RY),
            ordinaryRingedToposPullback IA ca
                ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M) ≅
              (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).obj
                (ordinaryRingedToposPullback I c M),
            (∀ (M N : ringedSiteModules.{u} (localCoefficientRings RY)) (h : M ⟶ N),
              changeOfRingsHom.{u, u, u} ca
                  (IA.modules.obj
                    ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M))
                  (IA.modules.map
                    ((elementModulePullback.{u, u} (localCoefficientRings RY) A).map h)) ≫
                  (e N).hom =
                (e M).hom ≫
                  (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).map
                    (changeOfRingsHom.{u, u, u} c (I.modules.obj M) (I.modules.map h))) ∧
            ∀ (M : ringedSiteModules.{u} (localCoefficientRings RY))
              (W : Cᵒᵖ) (b : (f.inverse.obj A).obj.obj W) (r : RX.obj.obj W)
              (m : (IA.modules.obj
                ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M)).val.obj
                  (elementObj (f.inverse.obj A) W b)),
              (e M).hom.val.app (elementObj (f.inverse.obj A) W b)
                  (((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
                    (𝟙 (localCoefficientRings
                      (presentationElementRing RX (f.inverse.obj A))).obj)).unit.app
                      (changeOfRingsPresheaf.{u, u, u} ca (IA.modules.obj
                        ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M)))).app
                          (elementObj (f.inverse.obj A) W b)
                            ((@id ((presentationElementRing RX (f.inverse.obj A)).obj.obj
                              (elementObj (f.inverse.obj A) W b)) r) ⊗ₜ[
                              RIA.obj.obj (elementObj (f.inverse.obj A) W b),
                              (ca.hom.app (elementObj (f.inverse.obj A) W b)).hom] m)) =
                ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
                  (𝟙 (localCoefficientRings RX).obj)).unit.app
                    (changeOfRingsPresheaf.{u, u, u} c (I.modules.obj M))).app W
                      (r ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom]
                        (@id ((I.modules.obj M).val.obj W)
                          ((IA.moduleUnderlying.hom.app
                            ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M) ≫
                          a.hom.app ((toSheaf.{u, u, u, u} (localCoefficientRings RY) ⋙
                            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
                          (elementSheafPullback (f.inverse.obj A)).map
                            (I.moduleUnderlying.inv.app M)).hom.app
                              (elementObj (f.inverse.obj A) W b) m))) := by
  classical
  have _ := slice
  intro RI I c hc
  let B := f.inverse.obj A
  let := f.leftExact
  let := fA.leftExact
  refine Exists.elim (algebraic_image (elementTopology A) (elementTopology B)
    fA.inverse fA.direct fA.adj (presentationElementRing RY A)) (fun RIA hIA ↦ ?_)
  refine Nonempty.elim hIA (fun IA ↦ ?_)
  have : PreservesFiniteLimits (elementSheafPullback A) := by
    rw [← y.localization_inverse]
    exact y.localization.leftExact
  let P := sliceComposite (elementSheafPullback A) fA.inverse (sliceRestriction RY A) IA
  let Q := sliceTransport a
    (sliceComposite f.inverse (elementSheafPullback B) I (sliceRestriction RI B))
  let d := sliceRingHom P Q
  have hd : (sheafCompose (elementTopology B)
      (CategoryTheory.forget CommRingCat.{u})).map d =
        P.ringUnderlying.inv ≫ Q.ringUnderlying.hom := by
    exact sliceRingHom_underlying P Q
  have hdi : IsIso d := by
    have : IsIso ((sheafCompose (elementTopology B)
        (CategoryTheory.forget CommRingCat.{u})).map d) := by rw [hd]; infer_instance
    exact isIso_of_reflects_iso d
      (sheafCompose (elementTopology B) (CategoryTheory.forget CommRingCat.{u}))
  let cB := sliceRingMap c B
  let ca := d ≫ cB
  have hd' : P.ringUnderlying.hom ≫
      (sheafCompose (elementTopology B)
        (CategoryTheory.forget CommRingCat.{u})).map d = Q.ringUnderlying.hom := by
    rw [hd, Iso.hom_inv_id_assoc]
  have hca : IA.ringUnderlying.hom ≫
      (sheafCompose (elementTopology B)
        (CategoryTheory.forget CommRingCat.{u})).map ca = fA.ringMap := by
    have h := congrArg (fun t ↦ t ≫
      (sheafCompose (elementTopology B)
        (CategoryTheory.forget CommRingCat.{u})).map cB) hd'
    have hp : P.ringUnderlying.hom = IA.ringUnderlying.hom := by
      change fA.inverse.map (𝟙 _) ≫ IA.ringUnderlying.hom = IA.ringUnderlying.hom
      rw [fA.inverse.map_id, Category.id_comp]
    rw [hp, Category.assoc, ← Functor.map_comp] at h
    refine h.trans ?_
    change (a.hom.app _ ≫
      ((elementSheafPullback B).map I.ringUnderlying.hom ≫ 𝟙 _)) ≫
        (elementSheafPullback B).map
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c) = fA.ringMap
    rw [Category.comp_id, Category.assoc, ← Functor.map_comp, hc]
    exact hr.symm
  refine Exists.elim (sliceModuleComparison P Q (@asIso _ _ _ _ d hdi) hd')
    (fun b hb ↦ ?_)
  have hb' (M : ringedSiteModules.{u} (localCoefficientRings RY)) :
      (toSheaf (localCoefficientRings RIA) ⋙
        sheafCompose (elementTopology B) (CategoryTheory.forget AddCommGrpCat.{u})).map
          (b.hom.app M) =
        IA.moduleUnderlying.hom.app
            ((elementModulePullback (localCoefficientRings RY) A).obj M) ≫
          a.hom.app ((toSheaf (localCoefficientRings RY) ⋙
            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
          (elementSheafPullback B).map (I.moduleUnderlying.inv.app M) := by
    exact (hb M).trans (sliceUnderlyingComparison RY RI A B f.inverse fA.inverse IA I a M)
  choose e he using fun M : ringedSiteModules.{u} (localCoefficientRings RY) ↦
    sliceTensorComparison c B (@asIso _ _ _ _ d hdi) ca rfl
      (P.modules.obj M) (I.modules.obj M) (b.app M)
  refine ⟨RIA, IA, ca, hca, e, ?_, ?_⟩
  · intro M N h
    exact sliceTensorComparisonNaturality c B (@asIso _ _ _ _ d hdi) ca
      P.modules I.modules b.hom e he M N h
  · intro M W w r m
    have h := he M (elementObj B W w) r m
    have hb'' := congrArg (fun q ↦ q.hom.app (elementObj B W w) m) (hb' M)
    exact h.trans (congrArg (slicePure c (I.modules.obj M) W r) hb'')

end SheafOfModules
