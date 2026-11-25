/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
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
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Composition of the ordered Tate coefficient along arbitrary maps

The proof reuses the general composition calculation underlying
`orderedTateExactOpenComposition`, exposing its left-derived form.
(blueprint: lem-pur-vector-integration-base-coefficient-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u u'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

private noncomputable def muHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleMuModulePresheaf T N ⟶
      P.obj ⋙ ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) where
  toFun f := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (f.app U).hom.toAddMonoidHom
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }⟩
  invFun f := {
    app := fun U ↦ ModuleCat.ofHom
      (X := finiteEtaleMuModuleObj T N U)
      (Y := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
      (AddMonoidHom.toZModLinearMap N
        (M := finiteEtaleMuModuleObj T N U)
        (M₁ := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
        (f.hom.app U).hom)
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private noncomputable def lineHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ P) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) :=
  ((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ P).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).whiskerRight
      T.Etaleᵒᵖ).homEquiv _ P.obj).trans (muHomEquiv T N A hA P))

private lemma lineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ P) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf N).obj.obj U) :
    (lineHomEquiv T N A hA P f).hom.app U z =
      f.hom.app U (finiteEtaleTateOneGenerator A N T hA U 1 z) := by
  dsimp [lineHomEquiv, muHomEquiv]
  change ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).homEquiv _ _
        ((toSheafify T.smallEtaleTopology _ ≫ f.hom).app U)) z = _
  rfl

private lemma lineHomEquiv_comp (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {P Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : finiteEtaleTateLine T N A hA ⟶ P) (g : P ⟶ Q) :
    lineHomEquiv T N A hA Q (f ≫ g) =
      lineHomEquiv T N A hA P f ≫
        (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g := by
  ext U z
  change g.hom.app U (f.hom.app U
    (finiteEtaleTateOneGenerator A N T hA U 1 z)) =
    g.hom.app U ((lineHomEquiv T N A hA P f).hom.app U z)
  rw [lineHomEquiv_generator]

private lemma transpose_composite
    (D : Type u') [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
    {X : Sheaf T.smallEtaleTopology D} {Y : Sheaf T'.smallEtaleTopology D}
    {Z : Sheaf T''.smallEtaleTopology D}
    (f : (Etale.upperStar D v).obj X ⟶ Y)
    (g : (Etale.upperStar D w).obj Y ⟶ Z) :
    (Etale.upperStarLowerStarAdjunction D (w ≫ v)).homEquiv _ _
      ((Etale.upperStarComp D w v).hom.app X ≫ (Etale.upperStar D w).map f ≫ g) =
    (Etale.upperStarLowerStarAdjunction D v).homEquiv _ _ f ≫
      (Etale.lowerStar D v).map
        ((Etale.upperStarLowerStarAdjunction D w).homEquiv _ _ g) ≫
      (Etale.lowerStarComp D w v).hom.app Z := by
  simp only [Adjunction.homEquiv_unit]
  rw [Functor.map_comp, reassoc_of% (Etale.upperStarComp_hom_app_unit_app D w v X),
    ← (Etale.lowerStarComp D w v).hom.naturality]
  have hn := (Etale.upperStarLowerStarAdjunction D w).unit.naturality f
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp,
    Functor.id_map, Category.assoc] at hn ⊢
  simp only [← Functor.map_comp_assoc (Etale.lowerStar D v)]
  rw [← reassoc_of% hn]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

open MonoidalCategory
attribute [local instance] Sheaf.monoidalCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory ordinaryFiniteSinglePullbackIso ordinaryFiniteSingleExactPullbackIso
attribute [local implicit_reducible] ordinaryFiniteDegreeZero

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor upperStar

private lemma normalized_roots_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (t.roots f hY).hom = Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf N f := by
  apply (cancel_mono (kernel.ι (N • 𝟙 X.gmSheaf))).mp
  rw [← t.roots_normalization,
    Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι]

private lemma normalized_line_transpose (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (N : Γ(T, ⊤)))
    (P : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A))
    (g : Scheme.finiteEtaleTateLine T' N A hA ⟶ P) :
    Scheme.lineHomEquiv T N A hA _
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
          ((t.line v hT).hom ≫ g)) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _)
        (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf N v ≫
          Scheme.lineHomEquiv T' N A hA P g) := by
  rw [Adjunction.homEquiv_naturality_right, Scheme.lineHomEquiv_comp,
    Adjunction.homEquiv_naturality_right]
  ext W z
  change ((lowerStar (ModuleCat.{u + 1} A) v).map g).hom.app W
      ((Scheme.lineHomEquiv T N A hA _
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
          (t.line v hT).hom)).hom.app W z) = _
  rw [Scheme.lineHomEquiv_generator, t.line_normalization, normalized_roots_eq]
  exact (Scheme.lineHomEquiv_generator T' N A hA P g _ _).symm

private lemma normalized_line_comp (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) :
    (upperStarComp (ModuleCat.{u + 1} A) w v).hom.app
        (Scheme.finiteEtaleTateLine T N A hA) ≫
      (upperStar (ModuleCat.{u + 1} A) w).map (t.line v hT).hom ≫
        (t.line w hT').hom = (t.line (w ≫ v) hT).hom := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (w ≫ v)).homEquiv
    _ _).injective
  apply (Scheme.lineHomEquiv T N A hA _).injective
  rw [Scheme.transpose_composite (ModuleCat.{u + 1} A) v w]
  rw [← Category.assoc, ← Adjunction.homEquiv_naturality_right]
  rw [Scheme.lineHomEquiv_comp, normalized_line_transpose]
  have hw := normalized_line_transpose A N hA t w hT'
    (Scheme.finiteEtaleTateLine T'' N A hA) (𝟙 _)
  simp only [Category.comp_id] at hw
  rw [hw]
  have hvw := normalized_line_transpose A N hA t (w ≫ v) hT
    (Scheme.finiteEtaleTateLine T'' N A hA) (𝟙 _)
  simp only [Category.comp_id] at hvw
  rw [hvw, ← Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp N w v]
  conv_rhs =>
    rw [Adjunction.homEquiv_naturality_right,
      Scheme.transpose_composite AddCommGrpCat.{u + 1} v w]
  erw [Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]
  have hforget :
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map
          ((lowerStarComp (ModuleCat.{u + 1} A) w v).hom.app
            (Scheme.finiteEtaleTateLine T'' N A hA)) =
        (lowerStarComp AddCommGrpCat.{u + 1} w v).hom.app
          ((sheafCompose T''.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj
              (Scheme.finiteEtaleTateLine T'' N A hA)) := rfl
  rw [hforget]
  conv_lhs => rw [Adjunction.homEquiv_naturality_right]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (lowerStarComp AddCommGrpCat.{u + 1} w v).hom.naturality
    (Scheme.lineHomEquiv T'' N A hA _ (𝟙 _))
  simp only [Functor.comp_map] at hn
  erw [hn]

private lemma normalized_line_comp_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    (hw : w = p ≫ v) (hS : IsUnit (N : Γ(S, ⊤))) (hU : IsUnit (N : Γ(U, ⊤))) :
    (upperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app
        (Scheme.finiteEtaleTateLine S N A hA) ≫
      (upperStar (ModuleCat.{u + 1} A) p).map (t.line v hS).hom ≫
        (t.line p hU).hom = (t.line w hS).hom := by
  subst w
  exact normalized_line_comp A N hA t v p hS hU

attribute [local irreducible] lowerStar Scheme.finiteEtaleTateLine

-- Exact comparison calculations follow SfP1ChartExchange, LineComparisons.
/-- Cache the unshifted comparison before specializing the categories. -/
@[irreducible] private def singleComparisonHom
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    (F : C ⥤ D) (single : C₀ ⥤ C) (single' : D₀ ⥤ D) (pull : C₀ ⥤ D₀)
    (s : single ⋙ F ≅ pull ⋙ single') (K : C₀) (M : D₀) (a : pull.obj K ≅ M) :
    F.obj (single.obj K) ⟶ single'.obj M :=
  s.hom.app K ≫ single'.map a.hom

/-- Cache shifting a morphism before specializing the categories. -/
@[irreducible] private def shiftedHom
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {K : C} {M : D} (a : F.obj K ⟶ M) (n : ℤ) :
    F.obj (K⟦n⟧) ⟶ M⟦n⟧ :=
  (F.commShiftIso n).hom.app K ≫ a⟦n⟧'

/-- The exact degree-zero comparison through the cached embeddings. -/
@[irreducible] private def exactLine₀ (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :=
  singleComparisonHom (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (ordinaryFiniteSingleFunctor A Y) (ordinaryFiniteSingleFunctor A X)
    (upperStar (ModuleCat.{u + 1} A) f) (ordinaryFiniteSingleExactPullbackIso A f) K M a

/-- Shift the exact comparison while retaining the ordinary object interface. -/
@[irreducible] private def exactLine (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :=
  shiftedHom (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (exactLine₀ A f a) (2 : ℤ)

private theorem compared_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) [NatTrans.CommShift e.hom ℤ] {K : C} {M : D}
    (a : G.obj K ⟶ M) (n : ℤ) :
    (F.commShiftIso n).hom.app K ≫ (e.hom.app K ≫ a)⟦n⟧' =
      e.hom.app (K⟦n⟧) ≫ shiftedHom G a n := by
  simp only [shiftedHom, Functor.map_comp]
  rw [NatTrans.shift_app_comm_assoc]

private theorem compared_shift_iso
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) [NatTrans.CommShift e.hom ℤ]
    (single : C₀ ⥤ C) (single' : D₀ ⥤ D) (pull : C₀ ⥤ D₀)
    (s : single ⋙ G ≅ pull ⋙ single') (K : C₀) (M : D₀)
    (a : pull.obj K ≅ M) (n : ℤ) :
    ((F.commShiftIso n).app (single.obj K) ≪≫
      (shiftFunctor D n).mapIso
        ((Functor.isoWhiskerLeft single e ≪≫ s).app K ≪≫ single'.mapIso a)).hom =
      e.hom.app ((single.obj K)⟦n⟧) ≫
        shiftedHom G (singleComparisonHom G single single' pull s K M a) n := by
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app]
  simp only [Category.assoc]
  unfold singleComparisonHom
  exact compared_shift e _ n

private theorem singleComparison_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteSinglePullbackIso A f =
      Functor.isoWhiskerLeft (ordinaryFiniteSingleFunctor A Y)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
      ordinaryFiniteSingleExactPullbackIso A f := by
  unfold ordinaryFiniteSinglePullbackIso
  rfl

private theorem shiftedSingle_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :
    letI : (ordinaryFinitePullback A f).CommShift ℤ :=
      commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
    (((ordinaryFinitePullback A f).commShiftIso (2 : ℤ)).app
        (ordinaryFiniteDegreeZero A Y K) ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        ((ordinaryFiniteSinglePullbackIso A f).app K ≪≫
          (ordinaryFiniteSingleFunctor A X).mapIso a)).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        ((ordinaryFiniteDegreeZero A Y K)⟦(2 : ℤ)⟧) ≫ exactLine A f a := by
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  have : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ℤ
  have : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom ℤ :=
    NatTrans.CommShift.of_iso_inv
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ℤ
  unfold exactLine exactLine₀
  rw [singleComparison_eq]
  exact compared_shift_iso
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (ordinaryFiniteSingleFunctor A Y) (ordinaryFiniteSingleFunctor A X)
    (upperStar (ModuleCat.{u + 1} A) f) (ordinaryFiniteSingleExactPullbackIso A f)
    K M a (2 : ℤ)

private theorem shiftedLine_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app _ ≫
        exactLine A f (t.line f hY) := by
  unfold ordinaryFiniteShiftedLinePullback
  exact shiftedSingle_eq A f (t.line f hY)

private theorem raw_single_coherence
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G) :
    Functor.whiskerLeft (DerivedCategory.singleFunctor C 0)
        (Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso F G).symm).hom ≫
      Functor.whiskerRight (F.mapDerivedCategorySingleFunctor 0).hom G.mapDerivedCategory ≫
      Functor.whiskerLeft F (G.mapDerivedCategorySingleFunctor 0).hom =
      (H.mapDerivedCategorySingleFunctor 0).hom ≫
        Functor.whiskerRight e.hom (DerivedCategory.singleFunctor E 0) := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Category.assoc]
  exact Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor F G H e K

private theorem singleComparisonHom_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (DF : D₀ ⥤ D₁) (DG : D₁ ⥤ D₂) (DH : D₀ ⥤ D₂)
    (e : H ≅ F ⋙ G) (de : DH ≅ DF ⋙ DG)
    (sF : S₀ ⋙ DF ≅ F ⋙ S₁) (sG : S₁ ⋙ DG ≅ G ⋙ S₂)
    (sH : S₀ ⋙ DH ≅ H ⋙ S₂)
    (hc : Functor.whiskerLeft S₀ de.hom ≫
        Functor.whiskerRight sF.hom DG ≫ Functor.whiskerLeft F sG.hom =
      sH.hom ≫ Functor.whiskerRight e.hom S₂)
    {K : C₀} {L : C₁} {M : C₂}
    (a : F.obj K ≅ L) (b : G.obj L ≅ M) (d : H.obj K ≅ M)
    (h : e.hom.app K ≫ G.map a.hom ≫ b.hom = d.hom) :
    de.hom.app (S₀.obj K) ≫
        DG.map (singleComparisonHom DF S₀ S₁ F sF K L a) ≫
          singleComparisonHom DG S₁ S₂ G sG L M b =
      singleComparisonHom DH S₀ S₂ H sH K M d := by
  unfold singleComparisonHom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := sG.hom.naturality a.hom
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hc' := congr_app hc K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc'
  rw [reassoc_of% hc']
  rw [← Functor.map_comp, ← Functor.map_comp, h]

private theorem raw_comparison_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G)
    {K : C} {L : D} {M : E} (a : F.obj K ≅ L) (b : G.obj L ≅ M)
    (d : H.obj K ≅ M) (h : e.hom.app K ≫ G.map a.hom ≫ b.hom = d.hom) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
          ((DerivedCategory.singleFunctor C 0).obj K) ≫
      G.mapDerivedCategory.map
        (singleComparisonHom F.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
          (DerivedCategory.singleFunctor D 0) F (F.mapDerivedCategorySingleFunctor 0) K L a) ≫
      singleComparisonHom G.mapDerivedCategory (DerivedCategory.singleFunctor D 0)
        (DerivedCategory.singleFunctor E 0) G (G.mapDerivedCategorySingleFunctor 0) L M b =
      singleComparisonHom H.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
        (DerivedCategory.singleFunctor E 0) H (H.mapDerivedCategorySingleFunctor 0) K M d := by
  exact singleComparisonHom_comp
    (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctor D 0)
    (DerivedCategory.singleFunctor E 0) F G H _ _ _ e _
    (F.mapDerivedCategorySingleFunctor 0) (G.mapDerivedCategorySingleFunctor 0)
    (H.mapDerivedCategorySingleFunctor 0) (raw_single_coherence F G H e) a b d h

private theorem exactLine₀_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    {K : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) g).obj K ≅ L)
    (b : (upperStar (ModuleCat.{u + 1} A) f).obj L ≅ M)
    (d : (upperStar (ModuleCat.{u + 1} A) fg).obj K ≅ M)
    (h : (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app K ≫
      (upperStar (ModuleCat.{u + 1} A) f).map a.hom ≫ b.hom = d.hom) :
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app (ordinaryFiniteDegreeZero A Z K) ≫
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
          (exactLine₀ A g a) ≫ exactLine₀ A f b = exactLine₀ A fg d := by
  unfold exactLine₀ ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
    ordinaryFiniteSingleExactPullbackIso
  exact raw_comparison_comp
    (upperStar (ModuleCat.{u + 1} A) g) (upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} A) fg)
    (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) a b d h

private theorem shift_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (e : H ≅ F ⋙ G) [NatTrans.CommShift e.hom ℤ]
    {K : C} {L : D} {M : E} (a : F.obj K ⟶ L) (b : G.obj L ⟶ M)
    (d : H.obj K ⟶ M) (h : e.hom.app K ≫ G.map a ≫ b = d) (n : ℤ) :
    e.hom.app (K⟦n⟧) ≫ G.map ((F.commShiftIso n).hom.app K ≫ a⟦n⟧') ≫
        (G.commShiftIso n).hom.app L ≫ b⟦n⟧' =
      (H.commShiftIso n).hom.app K ≫ d⟦n⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]
  have he := NatTrans.shift_app_comm e.hom n K
  simp only [Functor.commShiftIso_comp_hom_app] at he
  rw [← reassoc_of% he]
  simp only [← Functor.map_comp, h]

private theorem compared_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H') (c : H' ≅ F' ⋙ G')
    {K : C} {B : D} {V : E} (a : F'.obj K ⟶ B) (b : G'.obj B ⟶ V)
    (d : H'.obj K ⟶ V) (hc : c.hom.app K ≫ G'.map a ≫ b = d) :
    (eH ≪≫ c ≪≫ Functor.isoWhiskerRight eF.symm G' ≪≫
        Functor.isoWhiskerLeft F eG.symm).hom.app K ≫
      G.map (eF.hom.app K ≫ a) ≫ eG.hom.app B ≫ b = eH.hom.app K ≫ d := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  rw [← eG.inv.naturality_assoc]
  rw [← G'.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hc]

private theorem shifted_line_comp
    (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app
        ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A f).map (ordinaryFiniteShiftedLinePullback A N hA t g hZ).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
      (ordinaryFiniteShiftedLinePullback A N hA t fg hZ).hom := by
  let c := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  have hc₀ := exactLine₀_comp A f g fg hfg
    (t.line g hZ) (t.line f hY) (t.line fg hZ)
    (normalized_line_comp_eq A N hA t f g fg hfg hZ hY)
  have : NatTrans.CommShift c.hom ℤ := by
    dsimp only [c, Iso.trans_hom]
    infer_instance
  have hc := shift_composite
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) fg).mapDerivedCategory c
    (exactLine₀ A g (t.line g hZ)) (exactLine₀ A f (t.line f hY))
    (exactLine₀ A fg (t.line fg hZ)) hc₀ (2 : ℤ)
  have hc' : c.hom.app ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
      (exactLine A g (t.line g hZ)) ≫ exactLine A f (t.line f hY) =
    exactLine A fg (t.line fg hZ) := by
    simpa only [exactLine, shiftedHom, ordinaryFiniteLine, ordinaryFiniteDegreeZero,
      ordinaryFiniteSingleFunctor_eq, Category.assoc] using hc
  dsimp only [ordinaryFiniteLine, ordinaryFiniteDegreeZero] at hc'
  have h := compared_composite
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) fg) c
    (exactLine A g (t.line g hZ)) (exactLine A f (t.line f hY))
    (exactLine A fg (t.line fg hZ)) hc'
  dsimp only [ordinaryFinitePullback, ordinaryFiniteLine, ordinaryFiniteSingleFunctor,
    ordinaryFiniteDegreeZero] at h ⊢
  simp (config := { dsimp := false }) only [shiftedLine_eq, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, c, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc] at h ⊢
  exact h

private lemma tensor_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (c : H ≅ F ⋙ G)
    {X Y : C} {X' Y' : D} {X'' Y'' : E}
    (a : F.obj X ⟶ X') (b : F.obj Y ⟶ Y')
    (a' : G.obj X' ⟶ X'') (b' : G.obj Y' ⟶ Y'')
    (d : H.obj X ⟶ X'') (e : H.obj Y ⟶ Y'')
    (δF : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (δG : G.obj (F.obj X ⊗ F.obj Y) ⟶ G.obj (F.obj X) ⊗ G.obj (F.obj Y))
    (δG' : G.obj (X' ⊗ Y') ⟶ G.obj X' ⊗ G.obj Y')
    (δH : H.obj (X ⊗ Y) ⟶ H.obj X ⊗ H.obj Y)
    (hc : δH ≫ (c.hom.app X ⊗ₘ c.hom.app Y) =
      c.hom.app (X ⊗ Y) ≫ G.map δF ≫ δG)
    (hn : δG ≫ (G.map a ⊗ₘ G.map b) = G.map (a ⊗ₘ b) ≫ δG')
    (hx : c.hom.app X ≫ G.map a ≫ a' = d)
    (hy : c.hom.app Y ≫ G.map b ≫ b' = e) :
    c.hom.app (X ⊗ Y) ≫ G.map (δF ≫ (a ⊗ₘ b)) ≫ δG' ≫ (a' ⊗ₘ b') =
      δH ≫ (d ⊗ₘ e) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← reassoc_of% hc]
  simp only [tensorHom_comp_tensorHom, hx, hy]

private lemma tensor_mapIso_hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' L L' : DerivedCategoryModule A T} (e : K ≅ K') (c : L ≅ L') :
    (ordinaryFiniteTensorRightMapIso A T e c).hom = e.hom ⊗ₘ c.hom := by
  change e.hom ▷ L ≫ K' ◁ c.hom = e.hom ⊗ₘ c.hom
  rw [MonoidalCategory.tensorHom_def]

lemma coefficient_succ_hom (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (vectorIntegrationBaseCoefficientPullback A N hA t f hY (d + 1)).hom =
      (ordinaryFiniteTensorPullback A f (affineLinearBaseCoefficient A N hA Y d)
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)).hom ≫
      ((vectorIntegrationBaseCoefficientPullback A N hA t f hY d).hom ⊗ₘ
        (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom) := by
  change (_ ≪≫ ordinaryFiniteTensorRightMapIso A X _ _).hom = _
  rw [Iso.trans_hom, tensor_mapIso_hom]
  rfl

end AlgebraicGeometry.Etale
