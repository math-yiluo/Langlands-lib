/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarEndpointComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward
import all WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
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
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal

/-! # Composition of normalized scalar/direct-image mates

Source: diagonal tower coefficient changes, paragraph (2), scalar associativity.
(blueprint: lem-diagonal-scalar-restriction-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
section SquareComposition

universe a v w
variable {A B C A' B' C' : Type a}
  [Category.{v} A] [Category.{v} B] [Category.{v} C]
  [Category.{v} A'] [Category.{v} B'] [Category.{v} C']
  [Abelian A] [Abelian B] [Abelian C]
  [Abelian A'] [Abelian B'] [Abelian C']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B'] [HasDerivedCategory.{w} C']

private def exactComp (R : A ⥤ B) (S : B ⥤ C) (T : A ⥤ C)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] (r : R ⋙ S ≅ T) :
    R.mapDerivedCategory ⋙ S.mapDerivedCategory ≅ T.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso R S ≪≫ Functor.mapDerivedCategoryNatIso r

private lemma exactComp_hom_fac (R : A ⥤ B) (S : B ⥤ C) (T : A ⥤ C)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] (r : R ⋙ S ≅ T)
    (K : CochainComplex A ℤ) :
    (exactComp R S T r).hom.app (DerivedCategory.Q.obj K) ≫
        T.mapDerivedCategoryFactors.hom.app K =
      S.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        S.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app K) := by
  simp only [exactComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso R S).inv.app
    (DerivedCategory.Q.obj K))).1
  erw [Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

private lemma exactComp_fac (R : A ⥤ B) (S : B ⥤ C) (T : A ⥤ C)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] (r : R ⋙ S ≅ T)
    (K : CochainComplex A ℤ) :
    S.mapDerivedCategoryFactors.inv.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        S.mapDerivedCategory.map (R.mapDerivedCategoryFactors.inv.app K) ≫
        (exactComp R S T r).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app K) ≫
        T.mapDerivedCategoryFactors.inv.app K := by
  apply (cancel_mono (T.mapDerivedCategoryFactors.hom.app K)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [exactComp_hom_fac]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Category.comp_id]

open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.DiagonalTrace

-- The comparison theorem allows independently chosen universal derived models.
private lemma acyclic_square [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ A') (G : B ⥤ B') (U : A ⥤ B) (V : A' ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G)
    (hacyc : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj I))) :
    Nonempty (ExactSquareOfUniverses F G U V RF RG ordinary) := by
  obtain ⟨e, he, -⟩ := CategoryTheory.derivedCoefficientComparison F G U V
    U.mapDerivedCategory V.mapDerivedCategory
    U.mapDerivedCategoryFactors V.mapDerivedCategoryFactors
    RF.R RG.R RF.η RG.η RF.computation hacyc ordinary
  refine ⟨⟨e, ?_⟩⟩
  intro P
  have h := congrArg (fun t ↦
    V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      t ≫ RG.R.map (U.mapDerivedCategoryFactors.hom.app P)) (he P)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← RG.R.map_comp, Iso.inv_hom_id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

variable (F : A ⥤ A') (G : B ⥤ B') (H : C ⥤ C')
  (R : A ⥤ B) (S : B ⥤ C) (T : A ⥤ C)
  (R' : A' ⥤ B') (S' : B' ⥤ C') (T' : A' ⥤ C')
  [F.Additive] [G.Additive] [H.Additive]
  [R.Additive] [S.Additive] [T.Additive] [R'.Additive] [S'.Additive] [T'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
  [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
  (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G) (RH : DiagonalRightDerived H)
  (e : F ⋙ R' ≅ R ⋙ G) (d : G ⋙ S' ≅ S ⋙ H) (c : F ⋙ T' ≅ T ⋙ H)
  (r : R ⋙ S ≅ T) (s : R' ⋙ S' ≅ T')
  (se : ExactSquareOfUniverses F G R R' RF RG e)
  (sd : ExactSquareOfUniverses G H S S' RG RH d)
  (sc : ExactSquareOfUniverses F H T T' RF RH c)

include se in
private lemma full_square_fac (K : CochainComplex A ℤ) :
    R'.mapDerivedCategory.map (RF.η.app K) ≫ se.iso.hom.app (DerivedCategory.Q.obj K) =
      R'.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) ≫
        RG.η.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        RG.R.map (R.mapDerivedCategoryFactors.inv.app K) := by
  apply (cancel_mono (RG.R.map (R.mapDerivedCategoryFactors.hom.app K))).1
  simp only [Category.assoc, ← RG.R.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact se.normalization K

include se sd sc in
private lemma full_square_horizontal [Abelian.HasKInjectiveResolutions A]
    (he : ∀ K : A, S'.map (e.hom.app K) ≫ d.hom.app (R.obj K) ≫
      H.map (r.hom.app K) = s.hom.app (F.obj K) ≫ c.hom.app K) :
    Functor.whiskerRight se.iso.hom S'.mapDerivedCategory ≫
        Functor.whiskerLeft R.mapDerivedCategory sd.iso.hom ≫
        Functor.whiskerRight (exactComp R S T r).hom RH.R =
      Functor.whiskerLeft RF.R (exactComp R' S' T' s).hom ≫ sc.iso.hom := by
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := A))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨K, hK, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  have := RF.computation K hK
  apply (cancel_epi (S'.mapDerivedCategory.map
    (R'.mapDerivedCategory.map (RF.η.app K)))).1
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change S'.mapDerivedCategory.map (R'.mapDerivedCategory.map (RF.η.app K)) ≫
      S'.mapDerivedCategory.map (se.iso.hom.app (DerivedCategory.Q.obj K)) ≫
      sd.iso.hom.app (R.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      RH.R.map ((exactComp R S T r).hom.app (DerivedCategory.Q.obj K)) =
    S'.mapDerivedCategory.map (R'.mapDerivedCategory.map (RF.η.app K)) ≫
      (exactComp R' S' T' s).hom.app (RF.R.obj (DerivedCategory.Q.obj K)) ≫
      sc.iso.hom.app (DerivedCategory.Q.obj K)
  have hf := full_square_fac F G R R' RF RG e se K
  have hg := full_square_fac G H S S' RG RH d sd
    ((R.mapHomologicalComplex (.up ℤ)).obj K)
  have hn := sd.iso.hom.naturality (R.mapDerivedCategoryFactors.inv.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← S'.mapDerivedCategory.map_comp_assoc, hf]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hg]
  have hfac := S'.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hfac
  erw [reassoc_of% hfac]
  erw [← RH.R.map_comp, ← RH.R.map_comp]
  erw [exactComp_fac R S T r K]
  have hη := RH.η.naturality
    ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hη
  rw [Functor.map_comp]
  erw [← reassoc_of% hη]
  have hnat := (exactComp R' S' T' s).hom.naturality (RF.η.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [reassoc_of% hnat, full_square_fac F H T T' RF RH c sc K]
  rw [reassoc_of% (exactComp_hom_fac R' S' T' s
    ((F.mapHomologicalComplex (.up ℤ)).obj K))]
  have hh : (S'.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app
        ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (H.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app K) =
    (NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app K := by
    ext n
    exact he (K.X n)
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc]
  simp only [Category.assoc] at hh ⊢
  erw [hh]
  simp only [Functor.map_comp, Category.assoc]
  rfl
end SquareComposition

section MateComposition
variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  {LX : A ⥤ B} {UX : B ⥤ A} {MX : B ⥤ C} {VX : C ⥤ B}
  {LY : D ⥤ E} {UY : E ⥤ D} {MY : E ⥤ F} {VY : F ⥤ E}
  {NX : A ⥤ C} {WX : C ⥤ A} {NY : D ⥤ F} {WY : F ⥤ D}
  (ax : LX ⊣ UX) (bx : MX ⊣ VX) (cx : NX ⊣ WX)
  (ay : LY ⊣ UY) (by' : MY ⊣ VY) (cy : NY ⊣ WY)
  {G : A ⥤ D} {H : B ⥤ E} {I : C ⥤ F}
  (ka : H ⋙ UY ≅ UX ⋙ G) (kb : I ⋙ VY ≅ VX ⋙ H)
  (kc : I ⋙ WY ≅ WX ⋙ G) (rx : WX ≅ VX ⋙ UX) (ry : WY ≅ VY ⋙ UY)

private lemma mates_comp
    (hc : Functor.whiskerRight kb.hom UY ≫ Functor.whiskerLeft VX ka.hom ≫
        Functor.whiskerRight rx.inv G =
      Functor.whiskerLeft I ry.inv ≫ kc.hom) (K : A) :
    (Adjunction.pushHomOfComapIso cx cy kc).app K ≫
        I.map ((Adjunction.leftAdjointCompIso ax bx cx rx.symm).inv.app K) =
      (Adjunction.leftAdjointCompIso ay by' cy ry.symm).inv.app (G.obj K) ≫
        MY.map ((Adjunction.pushHomOfComapIso ax ay ka).app K) ≫
        (Adjunction.pushHomOfComapIso bx by' kb).app (LX.obj K) := by
  have hp := WeilConjectures.CompactSupportCondensedRealization.push_pasting_canonical
    ax bx cx ay by' cy ka kb kc rx ry hc K
  have hx := WeilConjectures.CompactSupportCondensedRealization.scalarComp_eq_conjugate
    ax bx cx rx.symm
  have hy := WeilConjectures.CompactSupportCondensedRealization.scalarComp_eq_conjugate
    ay by' cy ry.symm
  simp only [Iso.symm_symm_eq] at hx hy
  rw [hx, hy] at hp
  change (Adjunction.leftAdjointCompIso ay by' cy ry.symm).hom.app (G.obj K) ≫
      (Adjunction.pushHomOfComapIso cx cy kc).app K =
    MY.map ((Adjunction.pushHomOfComapIso ax ay ka).app K) ≫
      (Adjunction.pushHomOfComapIso bx by' kb).app (LX.obj K) ≫
      I.map ((Adjunction.leftAdjointCompIso ax bx cx rx.symm).hom.app K) at hp
  have hh := congrArg (fun t ↦
    (Adjunction.leftAdjointCompIso ay by' cy ry.symm).inv.app (G.obj K) ≫ t ≫
      I.map ((Adjunction.leftAdjointCompIso ax bx cx rx.symm).inv.app K)) hp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← I.map_comp,
    Iso.hom_inv_id_app] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  exact hh
end MateComposition

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Mod.monoidalCategory Mod.monoidalCategoryStruct
  Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

private theorem restriction_acyclic
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (I : CochainComplex (Modules Λ' X) ℤ) (hI : I.IsKInjective) :
    IsIso (R.η.app (((Mod.comap (coefficientMap a X)).mapHomologicalComplex
      (.up ℤ)).obj I)) := by
  classical
  let U : Modules Λ' X ⥤ Modules Λ X := Mod.comap (coefficientMap a X)
  let G := CondensedRing.lowerStar Λ f
  let L := CondensedRing.upperStar Λ f
  -- Exactness suffices here; do not use global preservation of K-flat complexes.
  let : L.PreservesKFlatQuasiIso :=
    { quasiIso_map := fun _ _ _ ↦ inferInstance }
  have : L.PreservesFlat := CondensedRing.upperStar_preservesFlat Λ f
  let UI := (U.mapHomologicalComplex (.up ℤ)).obj I
  obtain ⟨J, hJ, j, _, hj⟩ :=
    CategoryTheory.Abelian.HasKInjectiveResolutions.exists_isKInjective UI
  have : QuasiIso j := hj
  have : I.IsKInjective := hI
  have : J.IsKInjective := hJ
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (Modules Λ X) (.up ℤ)).map j)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using hj
  have hmap : IsIso (DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ _).map j))) := by
    refine isIso_map_of_adjoints
      ((Mod.extendRestrictAdjunction (coefficientMap a X)).mapHomotopyCategory (.up ℤ))
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ))
      (HomotopyCategory.quasiIso (Modules Λ X) (.up ℤ))
      (HomotopyCategory.quasiIso (Modules Λ S) (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules Λ X) (.up ℤ)).kFlat
      L.kFlatKFlatMap ?_ ?_ ?_ ?_ ?_
      ((HomotopyCategory.quotient _ _).obj I)
      (fun P ↦ CochainComplex.IsKInjective.Qh_map_bijective P I)
      ((HomotopyCategory.quotient _ _).obj J)
      (fun P ↦ CochainComplex.IsKInjective.Qh_map_bijective P J)
      ((HomotopyCategory.quotient _ _).map j)
    · intro P
      let r := Classical.arbitrary
        ((HomotopyCategory.quasiIso (Modules Λ X) (.up ℤ)).localizerMorphismKFlat.LeftResolution P)
      exact ⟨r.X₁.obj, r.w, r.X₁.property,
        Localization.inverts DerivedCategory.Qh _ _ r.hw⟩
    · intro P
      let r := Classical.arbitrary
        ((HomotopyCategory.quasiIsoLocalizerMorphism L.kFlatKFlatMap).LeftResolution P)
      exact ⟨r.X₁.obj, r.w, r.X₁.property,
        Localization.inverts DerivedCategory.Qh _ _ r.hw⟩
    · intro P Q hP hQ t ht
      exact (Mod.extendScalars (coefficientMap a X)).isIso_Qh_map_mapHomotopyCategory_map
        hP hQ t ((DerivedCategory.isIso_Qh_map_iff t).mp ht)
    · intro P Q hP hQ t ht
      exact L.isIso_Qh_map_mapHomotopyCategory_map hP.1 hQ.1 t
        ((DerivedCategory.isIso_Qh_map_iff t).mp ht)
    · intro P hP
      exact hP.2
  have hGj : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) := by
    rw [G.mapHomotopyCategory_map] at hmap
    exact (HomologicalComplex.mem_quasiIso_iff _).mp
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
        ((DerivedCategory.isIso_Qh_map_iff _).mp hmap))
  have := hGj
  have := R.computation J hJ
  have hn := R.η.naturality j
  dsimp only [Functor.comp_map] at hn
  have : IsIso (R.η.app UI ≫ R.R.map (DerivedCategory.Q.map j)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (R.R.map (DerivedCategory.Q.map j))

private def ordinaryRestrictionComp
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (h : a ≫ b = c) (X : Scheme.{u}) :
    Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientMap b X) ⋙
      Mod.comap (coefficientMap a X) ≅ Mod.comap (coefficientMap c X) :=
  (Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
    Mod.comapCongr (by rw [← h, coefficientMap_comp])

private lemma scalarRestrictionCompIso_inv
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (h : a ≫ b = c) (X : Scheme.{u}) :
    (scalarRestrictionCompIso a b c h X).inv =
      (exactComp (Mod.comap (coefficientMap b X)) (Mod.comap (coefficientMap a X))
        (Mod.comap (coefficientMap c X)) (ordinaryRestrictionComp a b c h X)).hom := rfl

private lemma ordinaryRestrictionComp_hom
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (h : a ≫ b = c) (X : Scheme.{u})
    (M : Modules Λ₂ X) :
    ((ordinaryRestrictionComp a b c h X).hom.app M).hom = 𝟙 M.X :=
  Category.id_comp _

private lemma ordinary_square_comp
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (h : a ≫ b = c)
    {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules Λ₂ X) :
    (Mod.comap (coefficientMap a S)).map ((CondensedRing.comapLowerStarIso b f).hom.app M) ≫
      (CondensedRing.comapLowerStarIso a f).hom.app
        ((Mod.comap (coefficientMap b X)).obj M) ≫
      (CondensedRing.lowerStar Λ₀ f).map ((ordinaryRestrictionComp a b c h X).hom.app M) =
    (ordinaryRestrictionComp a b c h S).hom.app ((CondensedRing.lowerStar Λ₂ f).obj M) ≫
      (CondensedRing.comapLowerStarIso c f).hom.app M := by
  apply Mod.hom_ext
  change ((CondensedRing.comapLowerStarIso b f).hom.app M).hom ≫
      ((CondensedRing.comapLowerStarIso a f).hom.app
        ((Mod.comap (coefficientMap b X)).obj M)).hom ≫
      ((f)_*[Ab.{u + 1}]).map (((ordinaryRestrictionComp a b c h X).hom.app M).hom) =
    ((ordinaryRestrictionComp a b c h S).hom.app
      ((CondensedRing.lowerStar Λ₂ f).obj M)).hom ≫
      ((CondensedRing.comapLowerStarIso c f).hom.app M).hom
  simp only [CondensedRing.comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom,
    ordinaryRestrictionComp_hom]
  change 𝟙 _ ≫ 𝟙 _ ≫ ((f)_*[Ab.{u + 1}]).map (𝟙 M.X) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- Normalized restriction squares exist for each coefficient leg, and their scalar
mates obey the composition equation for every derived object. No endpoint, line,
class, trace, integration identity or mate invertibility is asserted.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), scalar associativity;
the normalization is the full-unit equation of DiagonalTrace.ExactSquareOfUniverses.
(blueprint: lem-diagonal-scalar-restriction-composition).

Proof: Resolve the scalar restriction of a K-injective complex by a K-injective
complex. The localized-Hom acyclicity test for two adjunctions applies to scalar
extension/restriction and geometric inverse image/direct image: use K-flat test
resolutions, with geometric test resolutions whose inverse images are K-flat.
Inverse image preserves flat objects and is exact, so the direct image of this
resolution map is a quasi-isomorphism. Naturality of the supplied derived unit
then proves acyclicity of the restricted complex. The universal comparison of
the two composites, computed on K-injectives, supplies the normalized squares.
For composition, the ordinary square has identity underlying sheaf components.
Evaluate the two derived pastings on K-injective representatives, cancel the
invertible source unit, and apply the full-unit equations, including on the
possibly non-K-injective restriction. Naturality and the ordinary identity give
horizontal composition. Finally use canonical horizontal mate pasting under the
actual scalar adjunctions and cancel the endpoint associators. No preservation
of K-injectives by restriction, scalar flatness, or mate invertibility is used. -/
theorem scalarRestriction_comp
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (hcoeff : a ≫ b = c)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R₀ : DiagonalRightDerived (CondensedRing.lowerStar Λ₀ f))
    (R₁ : DiagonalRightDerived (CondensedRing.lowerStar Λ₁ f))
    (R₂ : DiagonalRightDerived (CondensedRing.lowerStar Λ₂ f)) :
    Nonempty (RestrictionSquare b f R₁ R₂) ∧
    Nonempty (RestrictionSquare c f R₀ R₂) ∧
    ∀ (s₀₁ : RestrictionSquare a f R₀ R₁)
      (s₁₂ : RestrictionSquare b f R₁ R₂) (s₀₂ : RestrictionSquare c f R₀ R₂)
      (K : DerivedCategory (Modules Λ₀ X)),
      (s₀₂.mate c).app K ≫ R₂.R.map ((scalarCompIso a b c hcoeff X).hom.app K) =
        (scalarCompIso a b c hcoeff S).hom.app (R₀.R.obj K) ≫
          (derivedScalars b S).map ((s₀₁.mate a).app K) ≫
          (s₁₂.mate b).app ((derivedScalars a X).obj K) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact acyclic_square _ _ _ _ R₂ R₁
      (CondensedRing.comapLowerStarIso b f) (restriction_acyclic b f R₁)
  · exact acyclic_square _ _ _ _ R₂ R₀
      (CondensedRing.comapLowerStarIso c f) (restriction_acyclic c f R₀)
  · intro s₀₁ s₁₂ s₀₂ K
    have hc := full_square_horizontal
      (CondensedRing.lowerStar Λ₂ f) (CondensedRing.lowerStar Λ₁ f)
      (CondensedRing.lowerStar Λ₀ f)
      (Mod.comap (coefficientMap b X)) (Mod.comap (coefficientMap a X))
      (Mod.comap (coefficientMap c X))
      (Mod.comap (coefficientMap b S)) (Mod.comap (coefficientMap a S))
      (Mod.comap (coefficientMap c S)) R₂ R₁ R₀
      (CondensedRing.comapLowerStarIso b f) (CondensedRing.comapLowerStarIso a f)
      (CondensedRing.comapLowerStarIso c f)
      (ordinaryRestrictionComp a b c hcoeff X) (ordinaryRestrictionComp a b c hcoeff S)
      s₁₂ s₀₁ s₀₂ (ordinary_square_comp a b c hcoeff f)
    rw [← scalarRestrictionCompIso_inv a b c hcoeff X,
      ← scalarRestrictionCompIso_inv a b c hcoeff S] at hc
    exact mates_comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b S))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c S))
      s₀₁.iso s₁₂.iso s₀₂.iso (scalarRestrictionCompIso a b c hcoeff X)
      (scalarRestrictionCompIso a b c hcoeff S) hc K

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
