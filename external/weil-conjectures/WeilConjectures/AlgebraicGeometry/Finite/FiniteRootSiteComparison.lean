/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonPullbackSections

/-! # Finite root comparison between the etale and pro-etale sites

Source: Stacks Project, proetale.tex, Tag 0GLZ, lemma-describe-pullback-from-etale;
sites-modules.tex, Tag 03EL, lemma-tensor-product-pullback
(blueprint: lem-amb-finite-root-site-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The recorded root module in the fixed `ZMod m` coefficient presentation.
Restriction along constant sections retains exactly the original root sections.
Source: Stacks Tags 03CY and 03PK (blueprint: lem-amb-finite-root-site-comparison). -/
def finiteRootProModule (T : Scheme.{u}) (m : ℕ) (hm : 0 < m) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ZMod m)) :=
  (sheafCompose (ProEt.topology T)
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv.{0, u + 1} (R := ZMod m)).symm.toRingHom)).obj
      ((constantRingModuleRestriction (ProEt.topology T) (ULift.{u + 1} (ZMod m))).obj
        (proEtaleRootsOfUnityModule T m hm))

/-- The actual balanced scalar extension of the root sheaf, sheafified sectionwise.
This is `D_m,T`, with the `A` factor first, as in the recorded etale construction.
Source: Stacks Tags 03EK and 03EL (blueprint: lem-amb-finite-root-site-comparison). -/
def finiteRootProTensor (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (T : Scheme.{u}) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A) :=
  (presheafToSheaf (ProEt.topology T) (ModuleCat.{u + 1} A)).obj
    ((finiteRootProModule T m hm).obj ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))

/-- A local tensor `z ⊗ a`, written `a ⊗ z`, followed by the sheafification unit.
Source: Stacks Tags 03EK and 03EL (blueprint: lem-amb-finite-root-site-comparison). -/
def finiteRootProGenerator (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (T : Scheme.{u}) (W : T.ProEtᵒᵖ) (a : A)
    (z : (proEtaleRootsOfUnitySheaf T m).obj.obj W) :
    (finiteRootProTensor A m hm hA T).obj.obj W :=
  (toSheafify (ProEt.topology T)
    ((finiteRootProModule T m hm).obj ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))).app W
        (a ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA] z)

attribute [irreducible] finiteRootProModule finiteRootProTensor finiteRootProGenerator

/-- The normalized comparison, with scalar, scheme, identity, composition and power laws.
The root comparison is the already constructed `ProEtale.cartierRootsIso`. Additive root
maps are linear for the unique constant `ZMod m` actions; the tensor arrows live in
`ModuleCat A` and hence are linear for the corresponding constant ring sheaves.
Source: Stacks Tags 0GLZ, 03CY and 03EL
(blueprint: lem-amb-finite-root-site-comparison). -/
def FiniteRootSiteComparisonSpec (A : Type (u + 1)) [CommRing A] : Prop :=
  ∃ (sigma : ∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) →
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (finiteEtaleTateLine T m A hA) ≅ finiteRootProTensor A m hm hA T)),
  ∃ (d : ∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T),
      (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).obj
        (finiteRootProTensor A m hm hA T) ⟶ finiteRootProTensor A m hm hA T'),
  /- root_sections: The section identification on every weakly etale test, through etale global
     sections. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (W : T.ProEt),
    ∃ e : ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        (T.rootsOfUnitySheaf m)).obj.obj (op W) ≃+
      ((Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj
        (T.rootsOfUnitySheaf m)).obj.obj (op (Etale.mk (𝟙 W.left))),
    ∀ x,
      ((proEtaleRootsOfUnityInclusion T m).hom.app (op W)
        ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app (op W) x)).down =
      ((kernel.ι (m • 𝟙 W.left.gmSheaf)).hom.app (op (Etale.mk (𝟙 W.left)))
        (((finiteEtaleTwistPullbackData A m hm hA).r W.hom hT).hom.hom.app
          (op (Etale.mk (𝟙 W.left))) (e x))).down) ∧
  /- root_unit: The root comparison takes a unit to the same unit after restriction. -/
  (∀ (m : ℕ) (hm : 0 < m) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (z : (T.rootsOfUnitySheaf m).obj.obj U),
    Additive.toMul (((proEtaleRootsOfUnityInclusion T m).hom.app W
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app W
        (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
          (T.rootsOfUnitySheaf m)).obj.map f.op
            (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
              (T.rootsOfUnitySheaf m)).hom.app U z)))).down) =
      Units.map f.left.appTop.hom.toMonoidHom
        (Additive.toMul (((kernel.ι (m • 𝟙 T.gmSheaf)).hom.app U z).down))) ∧
  /- tensor_unit: Balanced-tensor normalization, including restriction to arbitrary pro-etale
     tests. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj U),
    (sigma m hm hA T hT).hom.hom.app W
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (finiteEtaleTateLine T m A hA)).obj.map f.op
          (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
            (finiteEtaleTateLine T m A hA)).hom.app U
              (finiteEtaleTateOneGenerator A m T hA U a z))) =
    finiteRootProGenerator A m hm hA T W a
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app W
        (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
          (T.rootsOfUnitySheaf m)).obj.map f.op
            (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
              (T.rootsOfUnitySheaf m)).hom.app U z)))) ∧
  /- d_unit: The adjunct of d is scalar extension of the recorded projection map on roots. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (W : T.ProEtᵒᵖ) (a : A)
    (z : (proEtaleRootsOfUnitySheaf T m).obj.obj W),
    ((proEtaleSheafAdjunction v (ModuleCat.{u + 1} A)).homEquiv _ _
      (d m hm hA v)).hom.app W (finiteRootProGenerator A m hm hA T W a z) =
    finiteRootProGenerator A m hm hA T' ((proEtaleBaseChange v).op.obj W) a
      ((proEtaleRootsOfUnityDirectImageMap v m).hom.app W z)) ∧
  /- scheme_square: The specified comparison square, with kappa the inverse of the recorded mate. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))),
    (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).map
        (sigma m hm hA T hT).hom ≫ d m hm hA v =
    (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) v).inv.app
        (finiteEtaleTateLine T m A hA) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').map
        ((finiteEtaleTwistPullbackData A m hm hA).c v hT hT' 1).hom ≫
      (sigma m hm hA T' hT').hom) ∧
  /- d_isIso: Invertibility of d, for every scheme map. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T), IsUnit (m : Γ(T, ⊤)) → IsIso (d m hm hA v)) ∧
  /- root_square: The corresponding square before extending scalars. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))),
    (proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).map
        (ProEtale.cartierRootsIso T m hm hT).hom ≫
      proEtaleRootsOfUnityInverseImageMap v m =
    (ProEtale.comparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} v).inv.app
        (T.rootsOfUnitySheaf m) ≫
      (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T').map
        ((finiteEtaleTwistPullbackData A m hm hA).r v hT).hom ≫
      (ProEtale.cartierRootsIso T' m hm hT').hom) ∧
  /- d_id: The identity law uses the canonical inverse-image identity comparison. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u}),
    IsUnit (m : Γ(T, ⊤)) →
    d m hm hA (𝟙 T) = (ProEtale.proEtaleComparisonId (ModuleCat.{u + 1} A) T).hom.app
      (finiteRootProTensor A m hm hA T)) ∧
  /- d_comp: The composition law uses the canonical inverse-image composition comparison. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T'),
    IsUnit (m : Γ(T, ⊤)) →
    d m hm hA (w ≫ v) =
      (ProEtale.proEtaleComparisonComp (ModuleCat.{u + 1} A) w v).hom.app
        (finiteRootProTensor A m hm hA T) ≫
      (proEtaleSheafInverseImage w (ModuleCat.{u + 1} A)).map (d m hm hA v) ≫
      d m hm hA w) ∧
  /- root_id: Root pullback has the same identity normalization. -/
  (∀ (m : ℕ) (T : Scheme.{u}), 0 < m → IsUnit (m : Γ(T, ⊤)) →
    proEtaleRootsOfUnityInverseImageMap (𝟙 T) m =
      (ProEtale.proEtaleComparisonId AddCommGrpCat.{u + 1} T).hom.app
        (proEtaleRootsOfUnitySheaf T m)) ∧
  /- root_comp: Root pullback has the same composition normalization. -/
  (∀ (m : ℕ) {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T'),
    0 < m → IsUnit (m : Γ(T, ⊤)) →
    proEtaleRootsOfUnityInverseImageMap (w ≫ v) m =
      (ProEtale.proEtaleComparisonComp AddCommGrpCat.{u + 1} w v).hom.app
        (proEtaleRootsOfUnitySheaf T m) ≫
      (proEtaleSheafInverseImage w AddCommGrpCat.{u + 1}).map
        (proEtaleRootsOfUnityInverseImageMap v m) ≫
      proEtaleRootsOfUnityInverseImageMap w m) ∧
  /- powers: Power maps commute with root and tensor comparisons, with unchanged A scalars. -/
  (∀ (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (hdiv : m ∣ m')
    (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m' : Γ(T, ⊤))),
    ∃ (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
      (tE : finiteEtaleTateLine T m' A hA' ⟶ finiteEtaleTateLine T m A hA)
      (tP : finiteRootProTensor A m' hm' hA' T ⟶ finiteRootProTensor A m hm hA T),
    q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf) ∧
    (∀ (U : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj U),
      tE.hom.app U (finiteEtaleTateOneGenerator A m' T hA' U a z) =
        finiteEtaleTateOneGenerator A m T hA U a (q.hom.app U z)) ∧
    (∀ (W : T.ProEtᵒᵖ) (a : A) (z : (proEtaleRootsOfUnitySheaf T m').obj.obj W),
      tP.hom.app W (finiteRootProGenerator A m' hm' hA' T W a z) =
        finiteRootProGenerator A m hm hA T W a
          ((proEtaleRootsOfUnityTransition T m m' hm hm' hdiv).hom.app W z)) ∧
    ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map q ≫
        (ProEtale.cartierRootsIso T m hm hT).hom =
      (ProEtale.cartierRootsIso T m' hm' hT').hom ≫
        proEtaleRootsOfUnityTransition T m m' hm hm' hdiv) ∧
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map tE ≫
        (sigma m hm hA T hT).hom = (sigma m' hm' hA' T hT').hom ≫ tP))

private theorem rootComparison_inclusion (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (hT : IsUnit (m : Γ(T, ⊤))) :
    (ProEtale.cartierRootsIso T m hm hT).hom ≫ proEtaleRootsOfUnityInclusion T m =
      (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map
        (kernel.ι (m • 𝟙 T.gmSheaf)) ≫ ProEtale.cartierUnitsComparison T := by
  unfold ProEtale.cartierRootsIso ProEtale.cartierRootsComparison
    proEtaleRootsOfUnityInclusion
  exact kernel.lift_ι _ _ _

private theorem rootComparison_unit (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (hT : IsUnit (m : Γ(T, ⊤))) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    Additive.toMul (((proEtaleRootsOfUnityInclusion T m).hom.app W
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app W
        (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
          (T.rootsOfUnitySheaf m)).obj.map f.op
            (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
              (T.rootsOfUnitySheaf m)).hom.app U z)))).down) =
      Units.map f.left.appTop.hom.toMonoidHom
        (Additive.toMul (((kernel.ι (m • 𝟙 T.gmSheaf)).hom.app U z).down)) := by
  let adj := ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T
  have h : adj.homEquiv _ _
      ((ProEtale.cartierRootsIso T m hm hT).hom ≫ proEtaleRootsOfUnityInclusion T m) =
        (kernel.ι (m • 𝟙 T.gmSheaf)) ≫ (⟨𝟙 _⟩ : T.gmSheaf ⟶
          (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).obj
            (proEtaleUnitsSheaf T)) := by
    rw [rootComparison_inclusion, Adjunction.homEquiv_naturality_left]
    unfold ProEtale.cartierUnitsComparison
    erw [Equiv.apply_symm_apply]
  have hu := congrArg (fun g ↦ g.hom.app U z) h
  rw [Adjunction.homEquiv_unit] at hu
  have hn := congrArg (fun g ↦ g
      (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
        (T.rootsOfUnitySheaf m)).hom.app U z))
    (((ProEtale.cartierRootsIso T m hm hT).hom ≫
      proEtaleRootsOfUnityInclusion T m).hom.naturality f.op)
  change (proEtaleRootsOfUnityInclusion T m).hom.app W
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app W
        (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
          (T.rootsOfUnitySheaf m)).obj.map f.op
            (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
              (T.rootsOfUnitySheaf m)).hom.app U z))) =
    (proEtaleUnitsSheaf T).obj.map f.op
      ((proEtaleRootsOfUnityInclusion T m).hom.app
        (op ((toProEt T).obj U.unop))
        ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app
          (op ((toProEt T).obj U.unop))
          (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
            (T.rootsOfUnitySheaf m)).hom.app U z))) at hn
  change (proEtaleRootsOfUnityInclusion T m).hom.app
      (op ((toProEt T).obj U.unop))
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app
        (op ((toProEt T).obj U.unop))
        (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
          (T.rootsOfUnitySheaf m)).hom.app U z)) =
      (kernel.ι (m • 𝟙 T.gmSheaf)).hom.app U z at hu
  rw [hu] at hn
  exact congrArg (fun x ↦ Additive.toMul x.down) hn

private noncomputable def etaleMuHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
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

private noncomputable def etaleLineHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ P) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) :=
  ((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ P).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).whiskerRight
      T.Etaleᵒᵖ).homEquiv _ P.obj).trans (etaleMuHomEquiv T N A hA P))

private lemma etaleLineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ P) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf N).obj.obj U) :
    (etaleLineHomEquiv T N A hA P f).hom.app U z =
      f.hom.app U (finiteEtaleTateOneGenerator A N T hA U 1 z) := by
  dsimp [etaleLineHomEquiv, etaleMuHomEquiv]
  change ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).homEquiv _ _
        ((toSheafify T.smallEtaleTopology _ ≫ f.hom).app U)) z = _
  rfl

private lemma etaleLineHomEquiv_comp (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {P Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : finiteEtaleTateLine T N A hA ⟶ P) (g : P ⟶ Q) :
    etaleLineHomEquiv T N A hA Q (f ≫ g) =
      etaleLineHomEquiv T N A hA P f ≫
        (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g := by
  ext U z
  change g.hom.app U (f.hom.app U
    (finiteEtaleTateOneGenerator A N T hA U 1 z)) =
    g.hom.app U ((etaleLineHomEquiv T N A hA P f).hom.app U z)
  rw [etaleLineHomEquiv_generator]

attribute [local semireducible] finiteRootProModule finiteRootProTensor finiteRootProGenerator

set_option backward.isDefEq.respectTransparency.types false

private noncomputable def proMuHomEquiv (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :
    ((finiteRootProModule T N hN).obj ⟶
      P.obj ⋙ ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)) ≃
    (proEtaleRootsOfUnitySheaf T N ⟶
      (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) where
  toFun f := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (f.app U).hom.toAddMonoidHom
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }⟩
  invFun f := {
    app := fun U ↦ ModuleCat.ofHom
      (X := (finiteRootProModule T N hN).obj.obj U)
      (Y := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
      (AddMonoidHom.toZModLinearMap N
        (M := (finiteRootProModule T N hN).obj.obj U)
        (M₁ := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
        (f.hom.app U).hom)
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private noncomputable def proLineHomEquiv (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :
    (finiteRootProTensor A N hN hA T ⟶ P) ≃
    (proEtaleRootsOfUnitySheaf T N ⟶
      (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) :=
  ((sheafificationAdjunction (ProEt.topology T) (ModuleCat.{u + 1} A)).homEquiv _ P).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).whiskerRight
      T.ProEtᵒᵖ).homEquiv _ P.obj).trans (proMuHomEquiv T N hN A hA P))

private lemma proLineHomEquiv_generator (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (f : finiteRootProTensor A N hN hA T ⟶ P) (U : T.ProEtᵒᵖ)
    (z : (proEtaleRootsOfUnitySheaf T N).obj.obj U) :
    (proLineHomEquiv T N hN A hA P f).hom.app U z =
      f.hom.app U (finiteRootProGenerator A N hN hA T U 1 z) := by
  dsimp [proLineHomEquiv, proMuHomEquiv]
  change ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).homEquiv _ _
        ((toSheafify (ProEt.topology T) _ ≫ f.hom).app U)) z = _
  rfl

private lemma proLineHomEquiv_comp (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {P Q : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)}
    (f : finiteRootProTensor A N hN hA T ⟶ P) (g : P ⟶ Q) :
    proLineHomEquiv T N hN A hA Q (f ≫ g) =
      proLineHomEquiv T N hN A hA P f ≫
        (sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g := by
  ext U z
  change g.hom.app U (f.hom.app U
    (finiteRootProGenerator A N hN hA T U 1 z)) =
    g.hom.app U ((proLineHomEquiv T N hN A hA P f).hom.app U z)
  rw [proLineHomEquiv_generator]

private def sigmaMap (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
      (finiteEtaleTateLine T m A hA) ⟶ finiteRootProTensor A m hm hA T :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).symm
    ((etaleLineHomEquiv T m A hA _).symm
      (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _)
        ((ProEtale.cartierRootsIso T m hm hT).hom ≫
          proLineHomEquiv T m hm A hA _ (𝟙 _))))

private def tensorPullbackMap (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) :
    (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).obj
      (finiteRootProTensor A m hm hA T) ⟶ finiteRootProTensor A m hm hA T' :=
  ((proEtaleSheafAdjunction v (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    ((proLineHomEquiv T m hm A hA _).symm
      (proEtaleRootsOfUnityDirectImageMap v m ≫
        (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
          (proLineHomEquiv T' m hm A hA _ (𝟙 _))))

private theorem sigmaMap_comp (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (P : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (g : finiteRootProTensor A m hm hA T ⟶ P) :
    etaleLineHomEquiv T m A hA _
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
          (sigmaMap A m hm hA T hT ≫ g)) =
      ((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _)
        ((ProEtale.cartierRootsIso T m hm hT).hom ≫
          proLineHomEquiv T m hm A hA P g) := by
  rw [Adjunction.homEquiv_naturality_right, etaleLineHomEquiv_comp]
  rw [sigmaMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hforget :
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map
          ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).map g) =
      (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).map
        ((sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g) := rfl
  rw [hforget, ← Adjunction.homEquiv_naturality_right]
  rw [Category.assoc, ← proLineHomEquiv_comp, Category.id_comp]

private theorem sigmaMap_isIso (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) :
    IsIso (sigmaMap A m hm hA T hT) := by
  apply isIso_of_coyoneda_map_bijective
  intro P
  let e := (proLineHomEquiv T m hm A hA P).trans
    ((Iso.homCongr (ProEtale.cartierRootsIso T m hm hT).symm (Iso.refl _)).trans
      (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _).trans
        ((etaleLineHomEquiv T m A hA _).symm.trans
          ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).symm)))
  suffices (fun g : finiteRootProTensor A m hm hA T ⟶ P ↦
      sigmaMap A m hm hA T hT ≫ g) = e by
    rw [this]
    exact e.bijective
  funext g
  apply ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).injective
  apply (etaleLineHomEquiv T m A hA _).injective
  simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact (sigmaMap_comp A m hm hA T hT P g).trans
    ((etaleLineHomEquiv T m A hA
      ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).obj P)).apply_symm_apply _).symm

private theorem etaleRootSections (S : Scheme.{u}) (N : ℕ) (U : S.Etaleᵒᵖ) :
    ∃! e : (S.rootsOfUnitySheaf N).obj.obj U ≃+
        Additive (rootsOfUnity N Γ(U.unop.left, ⊤)),
      ∀ x, ULift.up (Additive.ofMul (Additive.toMul (e x)).val) =
        (kernel.ι (N • 𝟙 S.gmSheaf)).hom.app U x := by
  let E := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U
  let φ := E.map (N • 𝟙 S.gmSheaf)
  let e := PreservesKernel.iso E (N • 𝟙 S.gmSheaf) ≪≫
    AddCommGrpCat.kernelIsoKer φ
  let g : φ.hom.ker ≃+
      Additive (rootsOfUnity N Γ(U.unop.left, ⊤)) :=
    { toFun := fun y ↦ Additive.ofMul ⟨y.1.down.toMul, by
        apply (mem_rootsOfUnity N _).2
        have hy : N • y.1 = 0 := y.2
        exact congrArg (fun z ↦ z.down.toMul) hy⟩
      invFun := fun y ↦ ⟨ULift.up (Additive.ofMul y.toMul.val), by
        change N • (ULift.up (Additive.ofMul y.toMul.val)) = 0
        apply ULift.ext
        apply Additive.toMul.injective
        exact (mem_rootsOfUnity N _).1 y.toMul.property⟩
      left_inv := fun y ↦ by rfl
      right_inv := fun y ↦ by rfl
      map_add' := fun y z ↦ by rfl }
  let e' := e.addCommGroupIsoToAddEquiv.trans g
  have he (x : (S.rootsOfUnitySheaf N).obj.obj U) :
      ULift.up (Additive.ofMul (Additive.toMul (e' x)).val) =
        (kernel.ι (N • 𝟙 S.gmSheaf)).hom.app U x := by
    change ((e.hom ≫ AddCommGrpCat.ofHom φ.hom.ker.subtype) x) = _
    rw [Iso.trans_hom, Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rfl
  refine ⟨e', he, ?_⟩
  intro e'' he''
  apply AddEquiv.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun y ↦ y.down.toMul) ((he'' x).trans (he x).symm)

private lemma etaleGenerator_smul (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) (W : T.Etaleᵒᵖ)
    (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    finiteEtaleTateOneGenerator A N T hA W a z =
      a • finiteEtaleTateOneGenerator A N T hA W 1 z := by
  unfold finiteEtaleTateOneGenerator
  let f := (toSheafify T.smallEtaleTopology
    (finiteEtaleMuModulePresheaf T N ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA))).app W
  exact (congrArg f (by
    simpa only [mul_one] using
      (ModuleCat.ExtendScalars.smul_tmul (finiteEtaleTwistScalar N A hA)
        (M := finiteEtaleMuModuleObj T N W) a 1 z).symm)).trans
    (f.hom.map_smul a _)

private lemma proGenerator_smul (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) (W : T.ProEtᵒᵖ)
    (a : A) (z : (proEtaleRootsOfUnitySheaf T N).obj.obj W) :
    finiteRootProGenerator A N hN hA T W a z =
      a • finiteRootProGenerator A N hN hA T W 1 z := by
  unfold finiteRootProGenerator
  let f := (toSheafify (ProEt.topology T)
    ((finiteRootProModule T N hN).obj ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA))).app W
  exact (congrArg f (by
    simpa only [mul_one] using
      (ModuleCat.ExtendScalars.smul_tmul (finiteEtaleTwistScalar N A hA)
        (M := (finiteRootProModule T N hN).obj.obj W) a 1 z).symm)).trans
    (f.hom.map_smul a _)

private theorem proGenerator_map (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    {U V : T.ProEtᵒᵖ} (f : U ⟶ V) (a : A)
    (z : (proEtaleRootsOfUnitySheaf T m).obj.obj U) :
    (finiteRootProTensor A m hm hA T).obj.map f
        (finiteRootProGenerator A m hm hA T U a z) =
      finiteRootProGenerator A m hm hA T V a
        ((proEtaleRootsOfUnitySheaf T m).obj.map f z) := by
  unfold finiteRootProTensor finiteRootProGenerator
  have h := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology T)
      ((finiteRootProModule T m hm).obj ⋙
        ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))).naturality f)
    (a ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA] z :
      (ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA)).obj
        ((finiteRootProModule T m hm).obj.obj U))
  exact h.symm

private theorem tensorPullbackMap_generator (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (W : T.ProEtᵒᵖ) (a : A)
    (z : (proEtaleRootsOfUnitySheaf T m).obj.obj W) :
    ((proEtaleSheafAdjunction v (ModuleCat.{u + 1} A)).homEquiv _ _
      (tensorPullbackMap A m hm hA v)).hom.app W
        (finiteRootProGenerator A m hm hA T W a z) =
      finiteRootProGenerator A m hm hA T' ((proEtaleBaseChange v).op.obj W) a
        ((proEtaleRootsOfUnityDirectImageMap v m).hom.app W z) := by
  let f := ((proEtaleSheafAdjunction v (ModuleCat.{u + 1} A)).homEquiv _ _
    (tensorPullbackMap A m hm hA v)).hom.app W
  have h1 : f (finiteRootProGenerator A m hm hA T W 1 z) =
      finiteRootProGenerator A m hm hA T' ((proEtaleBaseChange v).op.obj W) 1
        ((proEtaleRootsOfUnityDirectImageMap v m).hom.app W z) := by
    have h := congrArg (fun g ↦ g.hom.app W z)
      ((proLineHomEquiv T m hm A hA
        ((proEtaleSheafDirectImage v (ModuleCat.{u + 1} A)).obj
          (finiteRootProTensor A m hm hA T'))).apply_symm_apply
        (proEtaleRootsOfUnityDirectImageMap v m ≫
          (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
            (proLineHomEquiv T' m hm A hA _ (𝟙 _))))
    rw [proLineHomEquiv_generator] at h
    dsimp only [f, tensorPullbackMap]
    rw [Equiv.apply_symm_apply]
    exact h.trans (proLineHomEquiv_generator T' m hm A hA _ (𝟙 _)
      ((proEtaleBaseChange v).op.obj W) _)
  change f (finiteRootProGenerator A m hm hA T W a z) = _
  rw [proGenerator_smul, _root_.map_smul, h1]
  exact (proGenerator_smul T' m hm A hA _ a _).symm

private theorem sigmaMap_generator (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    (sigmaMap A m hm hA T hT).hom.app W
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (finiteEtaleTateLine T m A hA)).obj.map f.op
          (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
            (finiteEtaleTateLine T m A hA)).hom.app U
              (finiteEtaleTateOneGenerator A m T hA U a z))) =
    finiteRootProGenerator A m hm hA T W a
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app W
        (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
          (T.rootsOfUnitySheaf m)).obj.map f.op
            (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
              (T.rootsOfUnitySheaf m)).hom.app U z))) := by
  let g := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
    (sigmaMap A m hm hA T hT)).hom.app U
  let z' := (ProEtale.cartierRootsIso T m hm hT).hom.hom.app
    (op ((toProEt T).obj U.unop))
    (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
      (T.rootsOfUnitySheaf m)).hom.app U z)
  have h1 : g (finiteEtaleTateOneGenerator A m T hA U 1 z) =
      finiteRootProGenerator A m hm hA T (op ((toProEt T).obj U.unop)) 1 z' := by
    have h := congrArg (fun k ↦ k.hom.app U z)
      (sigmaMap_comp A m hm hA T hT (finiteRootProTensor A m hm hA T) (𝟙 _))
    rw [Category.comp_id, etaleLineHomEquiv_generator] at h
    rw [Adjunction.homEquiv_unit] at h
    exact h.trans (proLineHomEquiv_generator T m hm A hA _ (𝟙 _) _ _)
  have ha : g (finiteEtaleTateOneGenerator A m T hA U a z) =
      finiteRootProGenerator A m hm hA T (op ((toProEt T).obj U.unop)) a z' := by
    rw [etaleGenerator_smul, _root_.map_smul, h1]
    exact (proGenerator_smul T m hm A hA _ a z').symm
  have hn := ConcreteCategory.congr_hom ((sigmaMap A m hm hA T hT).hom.naturality f.op)
    (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
      (finiteEtaleTateLine T m A hA)).hom.app U
      (finiteEtaleTateOneGenerator A m T hA U a z))
  change _ = (finiteRootProTensor A m hm hA T).obj.map f.op
    (g (finiteEtaleTateOneGenerator A m T hA U a z)) at hn
  rw [ha, proGenerator_map] at hn
  have hz := ConcreteCategory.congr_hom
    ((ProEtale.cartierRootsIso T m hm hT).hom.hom.naturality f.op)
    (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
      (T.rootsOfUnitySheaf m)).hom.app U z)
  exact hn.trans (congrArg (finiteRootProGenerator A m hm hA T W a) hz.symm)

private theorem rootComparison_sections (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (W : T.ProEt) :
    ∃ e : ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        (T.rootsOfUnitySheaf m)).obj.obj (op W) ≃+
      ((Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj
        (T.rootsOfUnitySheaf m)).obj.obj (op (Etale.mk (𝟙 W.left))),
    ∀ x,
      ((proEtaleRootsOfUnityInclusion T m).hom.app (op W)
        ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app (op W) x)).down =
      ((kernel.ι (m • 𝟙 W.left.gmSheaf)).hom.app (op (Etale.mk (𝟙 W.left)))
        (((finiteEtaleTwistPullbackData A m hm hA).r W.hom hT).hom.hom.app
          (op (Etale.mk (𝟙 W.left))) (e x))).down := by
  let r := ((finiteEtaleTwistPullbackData A m hm hA).r W.hom hT)
  let r₀ := (((sheafToPresheaf _ _).mapIso r).app
    (op (Etale.mk (𝟙 W.left)))).addCommGroupIsoToAddEquiv
  let c := (((sheafToPresheaf _ _).mapIso
    (ProEtale.cartierRootsIso T m hm hT)).app (op W)).addCommGroupIsoToAddEquiv
  obtain ⟨eE, heE, _⟩ := etaleRootSections W.left m (op (Etale.mk (𝟙 W.left)))
  let eP := proEtaleRootsOfUnitySections T m (op W)
  have heP := (existsUnique_proEtaleRootsOfUnitySections T m (op W)).exists.choose_spec
  let e := c.trans (eP.trans (eE.symm.trans r₀.symm))
  refine ⟨e, ?_⟩
  intro x
  have hr : r₀ (e x) = eE.symm (eP (c x)) := by
    dsimp only [e, AddEquiv.trans_apply]
    exact r₀.apply_symm_apply _
  have hE := heE (eE.symm (eP (c x)))
  -- Transport the equality directly, avoiding rewriting through the evaluated sheaf objects.
  have hE' := (congrArg
    (fun y : Additive (rootsOfUnity m Γ(W.left, ⊤)) ↦
      ULift.up.{u + 1} (Additive.ofMul (Additive.toMul y).val))
    (eE.apply_symm_apply (eP (c x)))).symm.trans hE
  have hP := heP (c x)
  change ((proEtaleRootsOfUnityInclusion T m).hom.app (op W) (c x)).down =
    ((kernel.ι (m • 𝟙 W.left.gmSheaf)).hom.app
      (op (Etale.mk (𝟙 W.left))) (r₀ (e x))).down
  exact (congrArg ULift.down (hP.symm.trans hE')).trans
    (congrArg (fun y ↦ ((kernel.ι (m • 𝟙 W.left.gmSheaf)).hom.app
      (op (Etale.mk (𝟙 W.left))) y).down) hr.symm)

attribute [local implicit_reducible] MorphismProperty Scheme.Etale Scheme.ProEt
  Scheme.smallEtaleTopology Scheme.toProEt MorphismProperty.Over.pullback
  Functor.sheafPushforwardContinuous MorphismProperty.Comma.changeProp
  MorphismProperty.Over.mk Scheme.instCategoryEtale Scheme.instCategoryProEt
  Etale.upperStar ProEtale.comparisonUpperStar ProEtale.lowerStar
  finiteEtaleTateSheaf finiteEtaleTateTwist ProEtale.comparisonLowerStar
  ProEtale.comparisonAdjunction Etale.lowerStar proEtaleUnitsSheaf
  rootsOfUnitySheaf proEtaleRootsOfUnitySheaf proEtaleRootsOfUnityInclusion
  proEtaleUnitsPower

attribute [local irreducible] sigmaMap tensorPullbackMap
  etaleLineHomEquiv proLineHomEquiv etaleMuHomEquiv proMuHomEquiv

private theorem composite_transpose
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)
    (X : C) (Z : E) (f : (F ⋙ H).obj X ⟶ Z) :
    (adj₁.comp adj₂).homEquiv X Z f =
      adj₁.homEquiv X (I.obj Z) (adj₂.homEquiv (F.obj X) Z f) := by
  rw [Adjunction.comp_homEquiv]
  rfl

private theorem transpose_mate
    {C : Type*} {D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (δ : R₁ ⟶ R₂)
    (X : C) (Y : D) (f : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (((conjugateEquiv adj₁ adj₂).symm δ).app X ≫ f) =
      adj₁.homEquiv X Y f ≫ δ.app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm]
  rw [Category.assoc, ← δ.naturality, ← Category.assoc, ← Adjunction.homEquiv_unit]

private theorem transpose_comparison (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Y : Sheaf (ProEt.topology T') (ModuleCat.{u + 1} A))
    (f : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) v).obj X) ⟶ Y) :
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).comp
      (proEtaleSheafAdjunction v (ModuleCat.{u + 1} A))).homEquiv X Y
        ((ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) v).inv.app X ≫ f) =
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T')).homEquiv X Y f ≫
        (ProEtale.lowerStarCompComparisonLowerStarIso v (ModuleCat.{u + 1} A)).inv.app Y := by
  unfold ProEtale.comparisonCoefficientPullbackIso
  exact transpose_mate
    ((Etale.upperStarLowerStarAdjunction _ v).comp
      (ProEtale.comparisonAdjunction _ T'))
    ((ProEtale.comparisonAdjunction _ T).comp (proEtaleSheafAdjunction v _))
    (ProEtale.lowerStarCompComparisonLowerStarIso v _).inv X Y f

private theorem transpose_comparison_ab
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (X : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Y : Sheaf (ProEt.topology T') AddCommGrpCat.{u + 1})
    (f : (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T').obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj X) ⟶ Y) :
    ((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).comp
      (proEtaleSheafAdjunction v AddCommGrpCat.{u + 1})).homEquiv X Y
        ((ProEtale.comparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} v).inv.app X ≫ f) =
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).comp
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T')).homEquiv X Y f ≫
        (ProEtale.lowerStarCompComparisonLowerStarIso v AddCommGrpCat.{u + 1}).inv.app Y := by
  unfold ProEtale.comparisonCoefficientPullbackIso
  exact transpose_mate
    ((Etale.upperStarLowerStarAdjunction _ v).comp
      (ProEtale.comparisonAdjunction _ T'))
    ((ProEtale.comparisonAdjunction _ T).comp (proEtaleSheafAdjunction v _))
    (ProEtale.lowerStarCompComparisonLowerStarIso v _).inv X Y f

private theorem rootComparison_adjunct (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (hT : IsUnit (m : Γ(T, ⊤))) :
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
      ((ProEtale.cartierRootsIso T m hm hT).hom ≫ proEtaleRootsOfUnityInclusion T m) =
        (kernel.ι (m • 𝟙 T.gmSheaf)) ≫ (⟨𝟙 _⟩ : T.gmSheaf ⟶
          (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).obj
            (proEtaleUnitsSheaf T)) := by
  rw [rootComparison_inclusion, Adjunction.homEquiv_naturality_left]
  unfold ProEtale.cartierUnitsComparison
  erw [Equiv.apply_symm_apply]

private theorem rootDirectImage_inclusion {T T' : Scheme.{u}} (v : T' ⟶ T)
    (m : ℕ) (W : T.ProEtᵒᵖ) (z : (proEtaleRootsOfUnitySheaf T m).obj.obj W) :
    (proEtaleRootsOfUnityInclusion T' m).hom.app ((proEtaleBaseChange v).op.obj W)
        ((proEtaleRootsOfUnityDirectImageMap v m).hom.app W z) =
      ULift.up (Additive.ofMul
        (Units.map (pullback.fst W.unop.hom v).appTop.hom.toMonoidHom
          (Additive.toMul (((proEtaleRootsOfUnityInclusion T m).hom.app W z).down)))) := by
  have hβ := (existsUnique_proEtaleRootsOfUnityDirectImageMap v m).exists.choose_spec W z
  have heX := (existsUnique_proEtaleRootsOfUnitySections T' m
    ((proEtaleBaseChange v).op.obj W)).exists.choose_spec
      ((proEtaleRootsOfUnityDirectImageMap v m).hom.app W z)
  have heY := (existsUnique_proEtaleRootsOfUnitySections T m W).exists.choose_spec z
  change proEtaleRootsOfUnitySections T' m ((proEtaleBaseChange v).op.obj W)
    ((proEtaleRootsOfUnityDirectImageMap v m).hom.app W z) = _ at hβ
  change ULift.up (Additive.ofMul (Additive.toMul
    (proEtaleRootsOfUnitySections T' m ((proEtaleBaseChange v).op.obj W)
      ((proEtaleRootsOfUnityDirectImageMap v m).hom.app W z))).val) = _ at heX
  rw [hβ] at heX
  change ULift.up (Additive.ofMul (Additive.toMul
    (proEtaleRootsOfUnitySections T m W z)).val) = _ at heY
  rw [← heX, ← heY]
  rfl

private theorem rootComparison_adjunct_inclusion (T : Scheme.{u}) (m : ℕ)
    (hm : 0 < m) (hT : IsUnit (m : Γ(T, ⊤))) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    (proEtaleRootsOfUnityInclusion T m).hom.app (op ((toProEt T).obj U.unop))
      (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
        (ProEtale.cartierRootsIso T m hm hT).hom).hom.app U z) =
      (kernel.ι (m • 𝟙 T.gmSheaf)).hom.app U z := by
  have h := rootComparison_adjunct T m hm hT
  rw [Adjunction.homEquiv_naturality_right] at h
  exact congrArg (fun f ↦ f.hom.app U z) h

private theorem etaleRootPullback_adjunct_inclusion (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))) :
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
      ((finiteEtaleTwistPullbackData A m hm hA).r v hT).hom) ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} v).map
          (kernel.ι (m • 𝟙 T'.gmSheaf)) =
    (kernel.ι (m • 𝟙 T.gmSheaf)) ≫ gmSheafToLowerStarGmSheaf v := by
  have h := congrArg
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _)
      ((finiteEtaleTwistPullbackData A m hm hA).laws.2.1 v hT)
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right] at h
  unfold upperStarGmSheafToGmSheaf at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

private theorem rootComparison_power (T : Scheme.{u}) (m m' : ℕ)
    (hm : 0 < m) (hm' : 0 < m') (hdiv : m ∣ m')
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m' : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
    (hq : q ≫ kernel.ι (m • 𝟙 T.gmSheaf) =
      (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf)) :
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map q ≫
        (ProEtale.cartierRootsIso T m hm hT).hom =
      (ProEtale.cartierRootsIso T m' hm' hT').hom ≫
        proEtaleRootsOfUnityTransition T m m' hm hm' hdiv := by
  have : Mono (proEtaleRootsOfUnityInclusion T m) := by
    unfold proEtaleRootsOfUnityInclusion
    infer_instance
  apply (cancel_mono (proEtaleRootsOfUnityInclusion T m)).mp
  have ht : proEtaleRootsOfUnityTransition T m m' hm hm' hdiv ≫
      proEtaleRootsOfUnityInclusion T m =
        (m' / m) • proEtaleRootsOfUnityInclusion T m' := by
    unfold proEtaleRootsOfUnityTransition proEtaleRootsOfUnityInclusion
    rw [kernel.lift_ι]
    simp only [Preadditive.comp_nsmul, Category.comp_id]
  simp only [Category.assoc, rootComparison_inclusion, ht,
    ← Functor.map_comp_assoc, hq, Functor.map_nsmul,
    Preadditive.nsmul_comp, Preadditive.comp_nsmul]

private def proPowerMap (A : Type (u + 1)) [CommRing A] (m m' : ℕ)
    (hm : 0 < m) (hm' : 0 < m') (hdiv : m ∣ m')
    (hA : (m : A) = 0) (hA' : (m' : A) = 0) (T : Scheme.{u}) :
    finiteRootProTensor A m' hm' hA' T ⟶ finiteRootProTensor A m hm hA T :=
  (proLineHomEquiv T m' hm' A hA' _).symm
    (proEtaleRootsOfUnityTransition T m m' hm hm' hdiv ≫
      proLineHomEquiv T m hm A hA _ (𝟙 _))

private theorem proPowerMap_generator (A : Type (u + 1)) [CommRing A] (m m' : ℕ)
    (hm : 0 < m) (hm' : 0 < m') (hdiv : m ∣ m')
    (hA : (m : A) = 0) (hA' : (m' : A) = 0) (T : Scheme.{u})
    (W : T.ProEtᵒᵖ) (a : A) (z : (proEtaleRootsOfUnitySheaf T m').obj.obj W) :
    (proPowerMap A m m' hm hm' hdiv hA hA' T).hom.app W
        (finiteRootProGenerator A m' hm' hA' T W a z) =
      finiteRootProGenerator A m hm hA T W a
        ((proEtaleRootsOfUnityTransition T m m' hm hm' hdiv).hom.app W z) := by
  have h := congrArg (fun g ↦ g.hom.app W z)
    ((proLineHomEquiv T m' hm' A hA' _).apply_symm_apply
      (proEtaleRootsOfUnityTransition T m m' hm hm' hdiv ≫
        proLineHomEquiv T m hm A hA _ (𝟙 _)))
  rw [proLineHomEquiv_generator] at h
  change (proPowerMap A m m' hm hm' hdiv hA hA' T).hom.app W
    (finiteRootProGenerator A m' hm' hA' T W 1 z) = _ at h
  have h1 := h.trans (proLineHomEquiv_generator T m hm A hA _ (𝟙 _) W _)
  rw [proGenerator_smul, _root_.map_smul, h1]
  exact (proGenerator_smul T m hm A hA W a _).symm

private theorem sigmaMap_power (A : Type (u + 1)) [CommRing A] (m m' : ℕ)
    (hm : 0 < m) (hm' : 0 < m') (hdiv : m ∣ m')
    (hA : (m : A) = 0) (hA' : (m' : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m' : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
    (hq : q ≫ kernel.ι (m • 𝟙 T.gmSheaf) =
      (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf))
    (tE : finiteEtaleTateLine T m' A hA' ⟶ finiteEtaleTateLine T m A hA)
    (htE : ∀ (U : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj U),
      tE.hom.app U (finiteEtaleTateOneGenerator A m' T hA' U a z) =
        finiteEtaleTateOneGenerator A m T hA U a (q.hom.app U z)) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map tE ≫
        sigmaMap A m hm hA T hT =
      sigmaMap A m' hm' hA' T hT' ≫ proPowerMap A m m' hm hm' hdiv hA hA' T := by
  apply ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).injective
  apply (etaleLineHomEquiv T m' A hA' _).injective
  rw [Adjunction.homEquiv_naturality_left, sigmaMap_comp]
  have hleft : etaleLineHomEquiv T m' A hA' _
      (tE ≫ (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
        (sigmaMap A m hm hA T hT)) =
    q ≫ etaleLineHomEquiv T m A hA _
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
        (sigmaMap A m hm hA T hT)) := by
    ext U z
    rw [etaleLineHomEquiv_generator]
    change (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
      (sigmaMap A m hm hA T hT)).hom.app U)
        (tE.hom.app U (finiteEtaleTateOneGenerator A m' T hA' U 1 z)) = _
    rw [htE]
    exact (etaleLineHomEquiv_generator T m A hA _
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
        (sigmaMap A m hm hA T hT)) U (q.hom.app U z)).symm
  rw [hleft]
  have hs := sigmaMap_comp A m hm hA T hT (finiteRootProTensor A m hm hA T) (𝟙 _)
  rw [Category.comp_id] at hs
  rw [hs, ← Adjunction.homEquiv_naturality_left, ← Category.assoc,
    rootComparison_power T m m' hm hm' hdiv hT hT' q hq]
  unfold proPowerMap
  rw [Equiv.apply_symm_apply, Category.assoc]

private theorem sigmaMap_adjunct_generator (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (U : T.Etaleᵒᵖ) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
      (sigmaMap A m hm hA T hT)).hom.app U
        (finiteEtaleTateOneGenerator A m T hA U a z) =
    finiteRootProGenerator A m hm hA T (op ((toProEt T).obj U.unop)) a
      (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
        (ProEtale.cartierRootsIso T m hm hT).hom).hom.app U z) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (sigmaMap A m hm hA T hT).hom.app _
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
        (finiteEtaleTateLine T m A hA)).hom.app U
          (finiteEtaleTateOneGenerator A m T hA U a z)) =
    finiteRootProGenerator A m hm hA T _ a
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app _
        (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
          (T.rootsOfUnitySheaf m)).hom.app U z))
  have h := sigmaMap_generator A m hm hA T hT U
    (op ((toProEt T).obj U.unop)) (𝟙 _) a z
  rw [op_id] at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
  exact h

private theorem rootComparison_adjunct_square (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
    (U : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    (proEtaleRootsOfUnityDirectImageMap v m).hom.app (op ((toProEt T).obj U.unop))
        (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
          (ProEtale.cartierRootsIso T m hm hT).hom).hom.app U z) =
      (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T').homEquiv _ _
          (ProEtale.cartierRootsIso T' m hm hT').hom).hom.app
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          ((finiteEtaleTwistPullbackData A m hm hA).r v hT).hom).hom.app U z)) := by
  have : Mono (proEtaleRootsOfUnityInclusion T' m) := by
    unfold proEtaleRootsOfUnityInclusion
    infer_instance
  have : Mono (proEtaleRootsOfUnityInclusion T' m).hom :=
    (sheafToPresheaf _ _).map_mono _
  apply (AddCommGrpCat.mono_iff_injective
    ((proEtaleRootsOfUnityInclusion T' m).hom.app
      ((proEtaleBaseChange v).op.obj (op ((toProEt T).obj U.unop))))).mp inferInstance
  rw [rootDirectImage_inclusion, rootComparison_adjunct_inclusion]
  erw [rootComparison_adjunct_inclusion T' m hm hT'
    ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)]
  exact (congrArg (fun f ↦ f.hom.app U z)
    (etaleRootPullback_adjunct_inclusion A m hm hA v hT)).symm

private theorem rightComparison_component
    (D : Type*) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (G : Sheaf (ProEt.topology T') D) (U : T.Etaleᵒᵖ) :
    ((ProEtale.lowerStarCompComparisonLowerStarIso v D).inv.app G).hom.app U =
      𝟙 (G.obj.obj ((proEtaleBaseChange v).op.obj ((toProEt T).op.obj U))) := by
  simp only [Functor.comp_obj, ProEtale.lowerStarCompComparisonLowerStarIso,
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, ProEtale.toProEtCompOverPullbackIso,
    ObjectProperty.ι_obj, Iso.refl_symm, Iso.trans_inv, Iso.refl_inv, Category.assoc,
    NatTrans.comp_app, NatTrans.id_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerRight_app,
    Functor.op_obj, NatTrans.op_app, NatIso.ofComponents_hom_app, Iso.refl_hom, op_id]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp]
  rfl

private theorem rootComparison_square (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))) :
    (proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).map
        (ProEtale.cartierRootsIso T m hm hT).hom ≫
      proEtaleRootsOfUnityInverseImageMap v m =
    (ProEtale.comparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} v).inv.app
        (T.rootsOfUnitySheaf m) ≫
      (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T').map
        ((finiteEtaleTwistPullbackData A m hm hA).r v hT).hom ≫
      (ProEtale.cartierRootsIso T' m hm hT').hom := by
  apply (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).comp
    (proEtaleSheafAdjunction v AddCommGrpCat.{u + 1})).homEquiv _ _).injective
  rw [transpose_comparison_ab]
  rw [composite_transpose, composite_transpose]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  unfold proEtaleRootsOfUnityInverseImageMap
  erw [Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  ext U z
  change (proEtaleRootsOfUnityDirectImageMap v m).hom.app ((toProEt T).op.obj U)
      (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
        (ProEtale.cartierRootsIso T m hm hT).hom).hom.app U z) =
    ((ProEtale.lowerStarCompComparisonLowerStarIso v AddCommGrpCat.{u + 1}).inv.app
      (proEtaleRootsOfUnitySheaf T' m)).hom.app U
        ((((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T').homEquiv _ _
          (ProEtale.cartierRootsIso T' m hm hT').hom).hom.app
          ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
            ((finiteEtaleTwistPullbackData A m hm hA).r v hT).hom).hom.app U z))
  rw [rightComparison_component]
  exact rootComparison_adjunct_square A m hm hA v hT hT' U z

private theorem sigmaMap_square (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))) :
    (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).map
        (sigmaMap A m hm hA T hT) ≫ tensorPullbackMap A m hm hA v =
    (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) v).inv.app
        (finiteEtaleTateLine T m A hA) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').map
        ((finiteEtaleTwistPullbackData A m hm hA).c v hT hT' 1).hom ≫
      sigmaMap A m hm hA T' hT' := by
  apply (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).comp
    (proEtaleSheafAdjunction v (ModuleCat.{u + 1} A))).homEquiv _ _).injective
  rw [transpose_comparison]
  rw [composite_transpose, composite_transpose]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  apply (etaleLineHomEquiv T m A hA _).injective
  ext U z
  rw [etaleLineHomEquiv_generator, etaleLineHomEquiv_generator]
  change ((proEtaleSheafAdjunction v (ModuleCat.{u + 1} A)).homEquiv _ _
      (tensorPullbackMap A m hm hA v)).hom.app (op ((toProEt T).obj U.unop))
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
          (sigmaMap A m hm hA T hT)).hom.app U
            (finiteEtaleTateOneGenerator A m T hA U 1 z)) =
    ((ProEtale.lowerStarCompComparisonLowerStarIso v (ModuleCat.{u + 1} A)).inv.app
      (finiteRootProTensor A m hm hA T')).hom.app U
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T').homEquiv _ _
      (sigmaMap A m hm hA T' hT')).hom.app
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)
          (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
            ((finiteEtaleTwistPullbackData A m hm hA).c v hT hT' 1).hom).hom.app U
              (finiteEtaleTateOneGenerator A m T hA U 1 z)))
  rw [rightComparison_component]
  rw [sigmaMap_adjunct_generator, tensorPullbackMap_generator,
    (finiteEtaleTwistPullbackData A m hm hA).laws.2.2.1,
    sigmaMap_adjunct_generator, rootComparison_adjunct_square A m hm hA v hT hT']
  rfl

private theorem tensorPullbackMap_isIso (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))) :
    IsIso (tensorPullbackMap A m hm hA v) := by
  have hT' : IsUnit (m : Γ(T', ⊤)) := by
    simpa only [map_natCast] using hT.map v.appTop.hom
  have := sigmaMap_isIso A m hm hA T hT
  have := sigmaMap_isIso A m hm hA T' hT'
  have : IsIso ((proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).map
      (sigmaMap A m hm hA T hT) ≫ tensorPullbackMap A m hm hA v) := by
    rw [sigmaMap_square A m hm hA v hT hT']
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).map
      (sigmaMap A m hm hA T hT)) _

private theorem tensorPullbackMap_id (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) :
    tensorPullbackMap A m hm hA (𝟙 T) =
      (ProEtale.proEtaleComparisonId (ModuleCat.{u + 1} A) T).hom.app
        (finiteRootProTensor A m hm hA T) := by
  have := sigmaMap_isIso A m hm hA T hT
  apply (cancel_epi ((proEtaleSheafInverseImage (𝟙 T) (ModuleCat.{u + 1} A)).map
    (sigmaMap A m hm hA T hT))).mp
  rw [sigmaMap_square A m hm hA (𝟙 T) hT hT,
    (finiteEtaleTwistPullbackData A m hm hA).laws.2.2.2.2.2.2.1 T hT 1]
  have hk := (ProEtale.comparison_pullback_coherent.2.2 A).1 T
    (finiteEtaleTateLine T m A hA)
  change (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) (𝟙 T)).inv.app
      (finiteEtaleTateLine T m A hA) ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map
      ((ProEtale.etaleComparisonId (ModuleCat.{u + 1} A) T).hom.app
        (finiteEtaleTateLine T m A hA)) ≫ sigmaMap A m hm hA T hT = _
  change (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) (𝟙 T)).hom.app
      (finiteEtaleTateLine T m A hA) ≫ _ =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map _ at hk
  rw [← hk]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact (NatTrans.naturality _ (sigmaMap A m hm hA T hT)).symm

private theorem sigmaMap_square_forward (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').map
        ((finiteEtaleTwistPullbackData A m hm hA).c v hT hT' 1).hom ≫
      sigmaMap A m hm hA T' hT' =
    (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) v).hom.app
        (finiteEtaleTateLine T m A hA) ≫
      (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).map
        (sigmaMap A m hm hA T hT) ≫ tensorPullbackMap A m hm hA v := by
  rw [sigmaMap_square, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem roots_map_inclusion (T : Scheme.{u}) (m : ℕ)
    {U V : T.ProEtᵒᵖ} (f : U ⟶ V)
    (z : (proEtaleRootsOfUnitySheaf T m).obj.obj U) :
    (proEtaleRootsOfUnityInclusion T m).hom.app V
      ((proEtaleRootsOfUnitySheaf T m).obj.map f z) =
    (proEtaleUnitsSheaf T).obj.map f
      ((proEtaleRootsOfUnityInclusion T m).hom.app U z) := by
  exact (ConcreteCategory.congr_hom
    ((proEtaleRootsOfUnityInclusion T m).hom.naturality f) z)

private theorem transpose_iso
    {C : Type*} {D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁)
    (X : C) (Y : D) (f : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (e.hom.app X ≫ f) =
      adj₁.homEquiv X Y f ≫ (conjugateIsoEquiv adj₁ adj₂ e).hom.app Y := by
  have h := transpose_mate adj₁ adj₂ (conjugateEquiv adj₁ adj₂ e.hom) X Y f
  rw [Equiv.symm_apply_apply] at h
  exact h

private theorem rootPullback_id (T : Scheme.{u}) (m : ℕ) :
    proEtaleRootsOfUnityInverseImageMap (𝟙 T) m =
      (ProEtale.proEtaleComparisonId AddCommGrpCat.{u + 1} T).hom.app
        (proEtaleRootsOfUnitySheaf T m) := by
  apply ((proEtaleSheafAdjunction (𝟙 T) AddCommGrpCat.{u + 1}).homEquiv _ _).injective
  unfold proEtaleRootsOfUnityInverseImageMap
  rw [Equiv.apply_symm_apply]
  have ht := transpose_mate (Adjunction.id (C := Sheaf (ProEt.topology T)
      AddCommGrpCat.{u + 1}))
    (proEtaleSheafAdjunction (𝟙 T) AddCommGrpCat.{u + 1})
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T)
        AddCommGrpCat.{u + 1} (ProEt.topology T)).inv
    (proEtaleRootsOfUnitySheaf T m) (proEtaleRootsOfUnitySheaf T m) (𝟙 _)
  rw [Category.comp_id] at ht
  change (proEtaleSheafAdjunction (𝟙 T) AddCommGrpCat.{u + 1}).homEquiv _ _
      ((ProEtale.proEtaleComparisonId AddCommGrpCat.{u + 1} T).hom.app
        (proEtaleRootsOfUnitySheaf T m)) = 𝟙 _ ≫ _ at ht
  rw [Category.id_comp] at ht
  refine Eq.trans ?_ ht.symm
  ext U z
  have : Mono (proEtaleRootsOfUnityInclusion T m) := by
    unfold proEtaleRootsOfUnityInclusion
    infer_instance
  have : Mono (proEtaleRootsOfUnityInclusion T m).hom :=
    (sheafToPresheaf _ _).map_mono _
  apply (AddCommGrpCat.mono_iff_injective
    ((proEtaleRootsOfUnityInclusion T m).hom.app
      ((proEtaleBaseChange (𝟙 T)).op.obj U))).mp inferInstance
  change (proEtaleRootsOfUnityInclusion T m).hom.app _
      ((proEtaleRootsOfUnityDirectImageMap (𝟙 T) m).hom.app U z) =
    (proEtaleRootsOfUnityInclusion T m).hom.app _
      ((proEtaleRootsOfUnitySheaf T m).obj.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U.unop).op z)
  rw [rootDirectImage_inclusion, roots_map_inclusion]
  rfl

private theorem coherent_tensor_comp
    {E₀ E₁ E₂ P₀ P₁ P₂ : Type*}
    [Category* E₀] [Category* E₁] [Category* E₂]
    [Category* P₀] [Category* P₁] [Category* P₂]
    (e₁ : E₀ ⥤ E₁) (e₂ : E₁ ⥤ E₂) (e₁₂ : E₀ ⥤ E₂)
    (p₁ : P₀ ⥤ P₁) (p₂ : P₁ ⥤ P₂) (p₁₂ : P₀ ⥤ P₂)
    (n₀ : E₀ ⥤ P₀) (n₁ : E₁ ⥤ P₁) (n₂ : E₂ ⥤ P₂)
    (ec : e₁₂ ⟶ e₁ ⋙ e₂) (pc : p₁₂ ⟶ p₁ ⋙ p₂)
    (k₁ : e₁ ⋙ n₁ ⟶ n₀ ⋙ p₁) (k₂ : e₂ ⋙ n₂ ⟶ n₁ ⋙ p₂)
    (k₁₂ : e₁₂ ⋙ n₂ ⟶ n₀ ⋙ p₁₂)
    (X₀ : E₀) (X₁ : E₁) (X₂ : E₂) (Y₀ : P₀) (Y₁ : P₁) (Y₂ : P₂)
    (s₀ : n₀.obj X₀ ⟶ Y₀) (s₁ : n₁.obj X₁ ⟶ Y₁) (s₂ : n₂.obj X₂ ⟶ Y₂)
    (c₁ : e₁.obj X₀ ⟶ X₁) (c₂ : e₂.obj X₁ ⟶ X₂) (c₁₂ : e₁₂.obj X₀ ⟶ X₂)
    (d₁ : p₁.obj Y₀ ⟶ Y₁) (d₂ : p₂.obj Y₁ ⟶ Y₂) (d₁₂ : p₁₂.obj Y₀ ⟶ Y₂)
    [Epi (k₁₂.app X₀ ≫ p₁₂.map s₀)]
    (hs₁ : n₁.map c₁ ≫ s₁ = k₁.app X₀ ≫ p₁.map s₀ ≫ d₁)
    (hs₂ : n₂.map c₂ ≫ s₂ = k₂.app X₁ ≫ p₂.map s₁ ≫ d₂)
    (hs₁₂ : n₂.map c₁₂ ≫ s₂ = k₁₂.app X₀ ≫ p₁₂.map s₀ ≫ d₁₂)
    (hc : c₁₂ = ec.app X₀ ≫ e₂.map c₁ ≫ c₂)
    (hk : n₂.map (ec.app X₀) ≫ k₂.app (e₁.obj X₀) ≫ p₂.map (k₁.app X₀) =
      k₁₂.app X₀ ≫ pc.app (n₀.obj X₀)) :
    d₁₂ = pc.app Y₀ ≫ p₂.map d₁ ≫ d₂ := by
  apply (cancel_epi (k₁₂.app X₀ ≫ p₁₂.map s₀)).mp
  rw [Category.assoc, ← hs₁₂, hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hs₂]
  have hn := k₂.naturality c₁
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, hs₁]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hk]
  congr 1
  have hp := pc.naturality s₀
  dsimp only [Functor.comp_map] at hp
  rw [← reassoc_of% hp]

private theorem tensorPullbackMap_comp (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
    (hT : IsUnit (m : Γ(T, ⊤))) :
    tensorPullbackMap A m hm hA (w ≫ v) =
      (ProEtale.proEtaleComparisonComp (ModuleCat.{u + 1} A) w v).hom.app
        (finiteRootProTensor A m hm hA T) ≫
      (proEtaleSheafInverseImage w (ModuleCat.{u + 1} A)).map
        (tensorPullbackMap A m hm hA v) ≫ tensorPullbackMap A m hm hA w := by
  have hT' : IsUnit (m : Γ(T', ⊤)) := by
    simpa only [map_natCast] using hT.map v.appTop.hom
  have hT'' : IsUnit (m : Γ(T'', ⊤)) := by
    simpa only [map_natCast] using hT'.map w.appTop.hom
  have := sigmaMap_isIso A m hm hA T hT
  have hc := congrArg Iso.hom
    ((finiteEtaleTwistPullbackData A m hm hA).laws.2.2.2.2.2.2.2.1
      v w hT hT' hT'' 1)
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hc
  have he : Etale.upperStarComp (ModuleCat.{u + 1} A) w v =
      ProEtale.etaleComparisonComp (ModuleCat.{u + 1} A) w v := by
    unfold Etale.upperStarComp ProEtale.etaleComparisonComp Etale.lowerStarComp
    rfl
  rw [he] at hc
  exact coherent_tensor_comp
    (Etale.upperStar (ModuleCat.{u + 1} A) v)
    (Etale.upperStar (ModuleCat.{u + 1} A) w)
    (Etale.upperStar (ModuleCat.{u + 1} A) (w ≫ v))
    (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A))
    (proEtaleSheafInverseImage w (ModuleCat.{u + 1} A))
    (proEtaleSheafInverseImage (w ≫ v) (ModuleCat.{u + 1} A))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T')
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T'')
    (ProEtale.etaleComparisonComp (ModuleCat.{u + 1} A) w v).hom
    (ProEtale.proEtaleComparisonComp (ModuleCat.{u + 1} A) w v).hom
    (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) v).hom
    (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) w).hom
    (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) (w ≫ v)).hom
    _ _ _ _ _ _
    (sigmaMap A m hm hA T hT) (sigmaMap A m hm hA T' hT')
    (sigmaMap A m hm hA T'' hT'') _ _ _ _ _ _
    (sigmaMap_square_forward A m hm hA v hT hT')
    (sigmaMap_square_forward A m hm hA w hT' hT'')
    (sigmaMap_square_forward A m hm hA (w ≫ v) hT hT'') hc
    ((ProEtale.comparison_pullback_coherent.2.2 A).2.1
      T'' T' T w v (finiteEtaleTateLine T m A hA))

private theorem rootPullback_comp {T T' T'' : Scheme.{u}}
    (v : T' ⟶ T) (w : T'' ⟶ T') (m : ℕ) :
    proEtaleRootsOfUnityInverseImageMap (w ≫ v) m =
      (ProEtale.proEtaleComparisonComp AddCommGrpCat.{u + 1} w v).hom.app
        (proEtaleRootsOfUnitySheaf T m) ≫
      (proEtaleSheafInverseImage w AddCommGrpCat.{u + 1}).map
        (proEtaleRootsOfUnityInverseImageMap v m) ≫
      proEtaleRootsOfUnityInverseImageMap w m := by
  apply ((proEtaleSheafAdjunction (w ≫ v) AddCommGrpCat.{u + 1}).homEquiv _ _).injective
  rw [transpose_iso
    ((proEtaleSheafAdjunction v AddCommGrpCat.{u + 1}).comp
      (proEtaleSheafAdjunction w AddCommGrpCat.{u + 1}))]
  have hc : conjugateIsoEquiv
      ((proEtaleSheafAdjunction v AddCommGrpCat.{u + 1}).comp
        (proEtaleSheafAdjunction w AddCommGrpCat.{u + 1}))
      (proEtaleSheafAdjunction (w ≫ v) AddCommGrpCat.{u + 1})
      (ProEtale.proEtaleComparisonComp AddCommGrpCat.{u + 1} w v) =
    Functor.sheafPushforwardContinuousComp'
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).symm
      AddCommGrpCat.{u + 1} (ProEt.topology T) (ProEt.topology T')
        (ProEt.topology T'') := by
    change conjugateIsoEquiv
      ((ProEtale.proEtaleComparisonAdjunction AddCommGrpCat.{u + 1} v).comp
        (ProEtale.proEtaleComparisonAdjunction AddCommGrpCat.{u + 1} w))
      (ProEtale.proEtaleComparisonAdjunction AddCommGrpCat.{u + 1} (w ≫ v)) _ = _
    unfold ProEtale.proEtaleComparisonComp
    rw [conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]
    rfl
  rw [hc, Adjunction.comp_homEquiv]
  change _ = (proEtaleSheafAdjunction v AddCommGrpCat.{u + 1}).homEquiv _ _
    ((proEtaleSheafAdjunction w AddCommGrpCat.{u + 1}).homEquiv _ _
      ((proEtaleSheafInverseImage w AddCommGrpCat.{u + 1}).map
        (proEtaleRootsOfUnityInverseImageMap v m) ≫
          proEtaleRootsOfUnityInverseImageMap w m)) ≫ _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  unfold proEtaleRootsOfUnityInverseImageMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext U z
  have : Mono (proEtaleRootsOfUnityInclusion T'' m) := by
    unfold proEtaleRootsOfUnityInclusion
    infer_instance
  have : Mono (proEtaleRootsOfUnityInclusion T'' m).hom :=
    (sheafToPresheaf _ _).map_mono _
  apply (AddCommGrpCat.mono_iff_injective
    ((proEtaleRootsOfUnityInclusion T'' m).hom.app
      ((proEtaleBaseChange (w ≫ v)).op.obj U))).mp inferInstance
  change (proEtaleRootsOfUnityInclusion T'' m).hom.app _
      ((proEtaleRootsOfUnityDirectImageMap (w ≫ v) m).hom.app U z) =
    (proEtaleRootsOfUnityInclusion T'' m).hom.app _
      ((proEtaleRootsOfUnitySheaf T'' m).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app
          U.unop).op
        ((proEtaleRootsOfUnityDirectImageMap w m).hom.app
          ((proEtaleBaseChange v).op.obj U)
          ((proEtaleRootsOfUnityDirectImageMap v m).hom.app U z)))
  rw [roots_map_inclusion]
  change _ = (proEtaleUnitsSheaf T'').obj.map _
    ((proEtaleRootsOfUnityInclusion T'' m).hom.app
      ((proEtaleBaseChange w).op.obj ((proEtaleBaseChange v).op.obj U))
      ((proEtaleRootsOfUnityDirectImageMap w m).hom.app _
        ((proEtaleRootsOfUnityDirectImageMap v m).hom.app U z)))
  rw [rootDirectImage_inclusion, rootDirectImage_inclusion, rootDirectImage_inclusion]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  have hp := congrArg (fun f ↦ f.appTop)
    (MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := @WeaklyEtale) (Q := ⊤) w v U.unop)
  simp only [Hom.comp_appTop] at hp
  exact (congrArg (fun f ↦ f.hom
    (Additive.toMul (((proEtaleRootsOfUnityInclusion T m).hom.app U z).down)).val) hp).symm

/-- The finite root comparison with its specified scalar and scheme coherence exists.
Source: Stacks Project, proetale.tex, Tag 0GLZ; sites-modules.tex, Tag 03EL
(blueprint: lem-amb-finite-root-site-comparison).

Proof:
1. Use the existing Cartier root isomorphism and its kernel-inclusion formula. Evaluate
   the etale and pro-etale kernels to identify their sections with actual roots of
   unity. Composing these equivalences with normalized etale root pullback gives the
   required section equivalence. Transposing the Cartier units map proves the unit law;
   naturality then gives restriction to every pro-etale test.
2. Sheafification and extension/restriction of scalars give natural Hom equivalences
   from each root tensor to any A-module sheaf, with additive maps out of roots on the
   other side. Additive maps between Z/m-modules are automatically Z/m-linear. Combine
   these equivalences with the comparison adjunction and the Cartier root isomorphism
   to construct sigma. Precomposition with sigma is bijective, so sigma is invertible.
   The adjunction units give the formula on generators, with the A scalar unchanged.
3. Construct d by transposing the recorded projection map on pro-etale roots through
   the scalar-extension Hom equivalence and the scheme inverse-image adjunction.
   Its formula on every generator follows directly from these adjunctions.
4. Transpose the canonical comparison mate under the two composite adjunctions.
   Both root-square adjuncts pull units back along the same fibre-product projection;
   the monic inclusion into units proves their equality. The scalar Hom equivalences
   and normalized etale generator law give the tensor square. Its other factors are
   invertible, hence d is invertible whenever m is invertible on the base.
5. The canonical comparisons and normalized etale pullback give the tensor identity
   and composition laws. For roots, transpose the canonical identity and composition
   comparisons; their section maps are restriction along the fibre-product identity
   and associativity maps. Functoriality of global sections proves both laws.
6. Use the normalized etale exponent-change map q. Scalar extension of the recorded
   pro-etale power map defines tP. Its generator formula is the scalar-adjunction unit.
   Postcompose the root power square with its monic inclusion into units; naturality
   and integer linearity of Cartier comparison prove equality. The scalar Hom
   equivalences then prove the tensor power square. No nonempty, affine, Noetherian,
   finite-type or nonzero-ring hypothesis is introduced.
-/
theorem finiteRootSiteComparison (A : Type (u + 1)) [CommRing A] [Finite A] :
    FiniteRootSiteComparisonSpec A := by
  have (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
      (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) := sigmaMap_isIso A m hm hA T hT
  refine ⟨fun m hm hA T hT ↦ asIso (sigmaMap A m hm hA T hT),
    fun m hm hA _ _ v ↦ tensorPullbackMap A m hm hA v,
    rootComparison_sections A, (fun m hm T ↦ rootComparison_unit T m hm),
    sigmaMap_generator A,
    tensorPullbackMap_generator A, sigmaMap_square A, tensorPullbackMap_isIso A,
    rootComparison_square A, tensorPullbackMap_id A, tensorPullbackMap_comp A,
    fun m T _ _ ↦ rootPullback_id T m,
    fun m _ _ _ v w _ _ ↦ rootPullback_comp v w m, ?_⟩
  intro m m' hm hm' hdiv hA hA' T hT hT'
  obtain ⟨q, t, hq, ht, _⟩ :=
    (finiteEtaleTwistPullbackData A m hm hA).laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 m' hm' hdiv T hT'
  refine ⟨q, (t 1).hom, proPowerMap A m m' hm hm' hdiv hA hA' T,
    hq, ht, proPowerMap_generator A m m' hm hm' hdiv hA hA' T,
    rootComparison_power T m m' hm hm' hdiv hT hT' q hq,
    sigmaMap_power A m m' hm hm' hdiv hA hA' T hT hT' q hq (t 1).hom ht⟩

end AlgebraicGeometry.Scheme
