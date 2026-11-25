/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCompositeMateAdjunct
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarIteratedMatesAdjunct
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackIdentityNormalization

/-!
# Counit scalar maps and ordinary étale direct-image composition

Source: Stacks Project, sites-cohomology.tex, Tag 0E46 (remark-compose-base-change),
with Tags 07A6 and 0D6E for the canonical adjunctions and K-injective comparisons
(blueprint: lem-pur-etale-direct-image-scalar-composition).

The coefficient comparison is the existing `scalarMate`, whose transpose is the
scalar/pullback isomorphism followed by scalar extension of the geometric counit.
The compositors below are the universal right-derived comparisons, normalized by
K-injective resolutions, in the direction from composite to iterated direct image.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem transport_iterated_adjunct
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G G' : D ⥤ E} {R : D ⥤ C} {S : E ⥤ D}
    (a : F ⊣ R) (b : G ⊣ S) (e : F ≅ F') (f : G ≅ G')
    {X : C} {Y : E} (h : X ⟶ R.obj (S.obj Y)) :
    (((a.ofNatIsoLeft e).comp (b.ofNatIsoLeft f)).homEquiv X Y).symm h =
      G'.map (e.inv.app X) ≫ f.inv.app (F.obj X) ≫
        ((a.comp b).homEquiv X Y).symm h := by
  simp only [Adjunction.homEquiv_counit, Adjunction.comp_counit_app,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← G'.map_comp_assoc, e.inv.naturality h, G'.map_comp]
  rw [← f.inv.naturality_assoc, ← f.inv.naturality_assoc]
  simp only [Category.assoc]

private theorem derived_identity_comparison
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C]
    (G : C ⥤ C) [G.Additive] [Limits.PreservesFiniteLimits G]
    [Limits.PreservesFiniteColimits G] (e : G ≅ 𝟭 C) :
    Functor.rightDerivedFunctorNatIso e ≪≫
        (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryIdIso C =
      G.rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C := by
  apply Iso.ext
  apply G.rightDerivedFunctor.rightDerived_ext G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  ext K : 2
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, ← Category.assoc]
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    Functor.rightDerivedNatTrans_app]
  have hf := congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  have hi := congr_app (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf hi
  rw [hf]
  simp only [Category.assoc]
  rw [reassoc_of% hi]
  simp only [Functor.whiskerRight_app]
  have hn := Functor.mapDerivedCategoryNatIso_fach e K
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ G.mapDerivedCategoryFactorsh.inv.app K ≫ t ≫
      (𝟭 C).mapDerivedCategoryFactorsh.inv.app K ≫
      (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K)) hn.symm

private theorem identity_counit
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M : DerivedCategoryModule A T) :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).inv.app
        (R(lowerStar (ModuleCat.{u + 1} A) (𝟙 T)).obj M) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 T)).counit.app M =
    (Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} A) T) ≪≫
      (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso _).hom.app M := by
  let G := lowerStar (ModuleCat.{u + 1} A) (𝟙 T)
  let : Limits.PreservesFiniteColimits G :=
    Limits.preservesFiniteColimits_of_natIso (lowerStarId (ModuleCat.{u + 1} A) T).symm
  let F := upperStar (ModuleCat.{u + 1} A) (𝟙 T)
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 T)
  let d := G.rightDerivedFunctorIsoMapDerivedCategory
  let i := Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) T) ≪≫
    Functor.mapDerivedCategoryIdIso _
  have h := adj.mapDerivedCategoryAdjunction_counit_app_of_iso
    (upperStarId (ModuleCat.{u + 1} A) T) (lowerStarId (ModuleCat.{u + 1} A) T)
    (upperStarId_inv_app_counit_app (ModuleCat.{u + 1} A) T) M
  rw [derived_identity_comparison]
  change _ = d.hom.app M ≫
    (Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) T) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom.app M
  rw [← h]
  change _ = d.hom.app M ≫ i.inv.app (G.mapDerivedCategory.obj M) ≫
    (F.mapDerivedCategory.map (d.inv.app M) ≫
      F.leftDerivedFunctorIsoMapDerivedCategory.inv.app _ ≫ adj.derivedAdjunction.counit.app M)
  have hi : leftDerivedUpperStarId (ModuleCat.{u + 1} A) T =
      F.leftDerivedFunctorIsoMapDerivedCategory ≪≫ i := by
    apply Iso.ext
    simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso, F, i]
  rw [hi]
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  have hn := i.inv.naturality (d.inv.app M)
  dsimp only [Functor.id_map] at hn
  rw [← reassoc_of% hn]
  rw [Iso.hom_inv_id_app_assoc]
  rfl

/-- The counit coefficient mate commutes with composition of arbitrary scheme morphisms.
Source: Stacks Project, Tag 0E46 (remark-compose-base-change)
(blueprint: lem-pur-etale-direct-image-scalar-composition).

Proof:
1. The normalized direct-image comparison is adjunction-compatible by
   lem-sfb-ringed-derived-monoidal-comparisons. Thus the composite counit is the
   counit for r after r-pullback of the counit for s. Exact inverse image is the
   constant-ring module pullback by situation-conventions.
2. Apply lem-sf-scalar-pullback-composition: the K-flat-normalized scalar/pullback
   isomorphism for r followed by s is the pasted pair of scalar/pullback isomorphisms.
3. By definition-projection-formula-map--1 and situation-conventions,
   the transpose of each scalarMate is its scalar/pullback map followed by scalar
   extension of the A-counit.
4. Transport the source along scalar extension of the A-compositor and transpose
   both proposed arrows under the composite B-adjunction. For the composite mate,
   steps 1 and 2 give scalar extension of the r-counit and pulled-back s-counit,
   preceded by the two scalar/pullback comparisons.
5. For the iterated mates, naturality of the s-counit moves the r-mate through it.
6. Substitute the two transpose equations from step 3. Naturality of the r scalar/
   pullback comparison at the s-counit gives precisely the expression in step 4.
   Injectivity of the Hom bijection gives equality; undo the source transport.
All arguments use unbounded K-flat and K-injective models; neither coefficient
flatness nor invertibility of the coefficient mate is used. -/
theorem scalarMate_directImage_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (r : X ⟶ Y) (s : Y ⟶ Z)
    (M : DerivedCategoryModule A X) :
    (scalarMate φ (r ≫ s)).app M ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} B) r) (lowerStar (ModuleCat.{u + 1} B) s)
          (lowerStarComp (ModuleCat.{u + 1} B) r s)).inv.app
            ((scalarExtension φ X).obj M) =
      (scalarExtension φ Z).map
          ((Functor.rightDerivedFunctorCompIso'
            (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
            (lowerStarComp (ModuleCat.{u + 1} A) r s)).inv.app M) ≫
        (scalarMate φ s).app (R(lowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) s).map ((scalarMate φ r).app M) := by
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) s
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r
  let ea := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) s
  let eb := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) r
  let kA := Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
    (lowerStarComp (ModuleCat.{u + 1} A) r s)
  apply (cancel_epi ((scalarExtension φ Z).map (kA.hom.app M))).1
  simp only [← Functor.map_comp_assoc, kA, Iso.hom_inv_id_app]
  apply ((((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) s).comp
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)).homEquiv _ _).symm).injective
  erw [scalarMate_comp_homEquiv_symm φ r s M]
  conv_rhs =>
    rw [mapDerivedUpperStarLowerStarAdjunction_eq,
      mapDerivedUpperStarLowerStarAdjunction_eq, transport_iterated_adjunct]
  have h := scalarMate_iterated_adjunct φ r s M
  have hAdj : scalarIteratedAdjunct φ r s M =
      ((a.comp b).homEquiv _ _).symm := by
    funext t
    simp only [scalarIteratedAdjunct, a, b, Adjunction.homEquiv_counit,
      Adjunction.comp_counit_app, Functor.comp_map]
  rw [hAdj] at h
  erw [(scalarExtension φ Z).map_id]
  simp only [Category.id_comp]
  dsimp only [a, b] at h
  erw [h]
  simp only [mapDerivedUpperStarLowerStarAdjunction_eq,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Category.assoc]
  apply (cancel_epi ((upperStar (ModuleCat.{u + 1} B) r).mapDerivedCategory.map
    (ea.inv.app ((scalarExtension φ Z).obj
      (R(lowerStar (ModuleCat.{u + 1} A) s).obj
        (R(lowerStar (ModuleCat.{u + 1} A) r).obj M)))))).2
  erw [eb.inv.naturality_assoc, eb.inv.naturality_assoc]
  erw [(scalarPullbackIso φ r).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← (scalarExtension φ X).map_comp_assoc]
  rw [(leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) r).hom.naturality]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← (scalarExtension φ X).map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) r).hom.naturality_assoc]
  simp only [Functor.id_obj, Iso.hom_inv_id_app_assoc]
  rfl

/-- Under the canonical identity direct-image comparisons the coefficient mate is identity.
Source: Stacks Project, Tags 0E46, 07A6 and 0D6E, identity normalization
(blueprint: lem-pur-etale-direct-image-scalar-composition).

Proof (step 7 of the node): the canonical identity pullback compositor is identity
on K-flat representatives, and every object has such a representative by
lem-pc-kflat-resolution. Apply lem-sf-scalar-pullback-composition to two identity
maps. The identity scalar/pullback comparison is idempotent; it is invertible by
def-pur-etale-scalar-pullback-iso, so it is identity. The identity adjunction has
identity counit by lem-sfb-ringed-derived-monoidal-comparisons. The defining transpose
of scalarMate is therefore identity, and the Hom bijection gives the displayed
identity after the two canonical direct-image identifications. -/
theorem scalarMate_directImage_identity
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (M : DerivedCategoryModule A T) :
    (scalarMate φ (𝟙 T)).app M ≫
        (Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} B) T) ≪≫
          (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app ((scalarExtension φ T).obj M) =
      (scalarExtension φ T).map
        ((Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} A) T) ≪≫
          (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app M) := by
  let P := L(upperStar (ModuleCat.{u + 1} B) (𝟙 T))
  let Q := scalarExtension φ T
  let U := R(lowerStar (ModuleCat.{u + 1} A) (𝟙 T)).obj M
  have hl : (leftDerivedUpperStarId (ModuleCat.{u + 1} B) T).inv.app (Q.obj U) ≫
      (scalarPullbackIso φ (𝟙 T)).hom.app U =
      Q.map ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).inv.app U) := by
    apply (cancel_mono
      (Q.map ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app U))).1
    rw [Category.assoc, (leftDerivedUpperStarId_scalarExtension_normalization φ T).2.2 U]
    simp only [Q, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.id_obj]
    exact (scalarExtension φ T).map_id _ |>.symm
  rw [← identity_counit B T (Q.obj M)]
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} B) T).inv.naturality
    ((scalarMate φ (𝟙 T)).app M)
  dsimp only [Functor.id_map] at hn
  rw [reassoc_of% hn]
  have hm := mateEquiv_counit
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 T))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) (𝟙 T))
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ (𝟙 T)).hom) M
  change P.map ((scalarMate φ (𝟙 T)).app M) ≫ _ = _ at hm
  rw [hm, ← Category.assoc, hl, ← Q.map_comp, identity_counit]

end AlgebraicGeometry.Etale
