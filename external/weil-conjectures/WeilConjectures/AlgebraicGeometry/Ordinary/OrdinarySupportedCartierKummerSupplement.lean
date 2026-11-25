/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.AlgebraicGeometry.SupportedCartierBoundaryExistence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryPullback
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryScalar
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
import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummer

/-!
# Existence of an ordinary supported Cartier Kummer map

## References

* Stacks 03PL and 0A45
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem supportedConstantExchange_isIso
    (A : Type (u + 1)) [CommRing A] {D D' T T' : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v) :
    IsIso (supportedConstantExchange A i i' v w sq.toCommSq) := by
  let := isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
  unfold supportedConstantExchange
  infer_instance

private theorem ordinaryTwistTransport_exists
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    Nonempty (OrdinaryFiniteTwistTransport A N hA) := by
  obtain ⟨r, c, p, hcover, hr, hc, _⟩ := Scheme.etaleFiniteTwistPullback A N hN hA
  let t : OrdinaryFiniteTwistTransport A N hA :=
    { roots := r
      line := fun v hT ↦ c v hT (by simpa using hT.map v.appTop.hom) 1
      roots_normalization := hr
      line_normalization := fun v hT ↦
        hc v hT (by simpa using hT.map v.appTop.hom) }
  exact ⟨t⟩

section

-- Use the same category-instance proofs as the recorded derived module category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The supported Cartier Kummer morphism, with its defining relative boundary,
unit/Chern equation, Cartier-preserving pullback square, and derived scalar square.
The derived arrow is displayed explicitly; Ext is only its canonical degree-two
representative. The boundary determines that representative uniquely. Pullback and
scalar-extension representatives are themselves normalized by the same boundary.
-/
theorem ordinary_supported_kummer (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃ (κ : Ext
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        (Scheme.finiteEtaleTateLine T N A hA) 2)
      (c : (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) ⟶
        (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)
      (c₁ : Ext (ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2)
      (t : OrdinaryFiniteTwistTransport A N hA),
      c = supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
        (ordinaryFiniteConstant A D) (Scheme.finiteEtaleTateLine T N A hA) κ ∧
      SupportedKummerBoundary A N hA i hI hT κ ∧
      (∀ κ' : Ext
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        (Scheme.finiteEtaleTateLine T N A hA) 2,
        SupportedKummerBoundary A N hA i hI hT κ' → κ' = κ) ∧
      (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
        (c₁.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2) =
          supportedKummerChern A N hA i hI hT ∧
      supportedDerivedUnit A i ≫ c = c₁.hom ∧
      (∀ {D' T' : Scheme.{u}} (i' : D' ⟶ T') [IsClosedImmersion i']
        (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v)
        (hI' : i'.ker.IsInvertible),
        ∃ κ' : Ext
          ((lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D'))
          (Scheme.finiteEtaleTateLine T' N A hA) 2,
          SupportedKummerBoundary A N hA i' hI'
            (by simpa using hT.map v.appTop.hom) κ' ∧
          IsIso (supportedConstantExchange A i i' v w sq.toCommSq) ∧
          (Ext.mk₀ (supportedConstantExchange A i i' v w sq.toCommSq)).comp
              κ' (zero_add 2) =
            (κ.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) v)).comp
              (Ext.mk₀ (t.line v hT).hom) (add_zero 2)) ∧
      (∀ [NeZero N],
        ∃ κ₀ : Ext
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
            (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
          (Scheme.finiteEtaleTateLine T N (ULift.{u + 1} (ZMod N))
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N))) 2,
          SupportedKummerBoundary (ULift.{u + 1} (ZMod N)) N
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N)) i hI hT κ₀ ∧
          SupportedKummerScalar
            ((Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom) N
            (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
              (ZMod.natCast_self N)) hA i κ₀ κ) := by
  classical
  obtain ⟨κ, hκ, huniq⟩ := supported_cartier_boundary_existsUnique T N hN A hA hT i hI
  obtain ⟨t⟩ := ordinaryTwistTransport_exists A N hN hA
  let d := supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
    (ordinaryFiniteConstant A D) (Scheme.finiteEtaleTateLine T N A hA) κ
  let c₁ : Ext (ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2 :=
    Ext.homEquiv.symm (supportedDerivedUnit A i ≫ d)
  refine ⟨κ, d, c₁, t, rfl, hκ, huniq, ?_, ?_, ?_, ?_⟩
  · exact (supported_derived_unit_forget A i _ κ).trans
      (supported_kummer_chern_realization T N A hA hT i hI κ hκ)
  · exact Ext.homEquiv.apply_symm_apply _ |>.symm
  · intro D' T' i' _ v w sq hI'
    obtain ⟨κ', hκ', _⟩ := supported_cartier_boundary_existsUnique T' N hN A hA
      (by simpa using hT.map v.appTop.hom) i' hI'
    exact ⟨κ', hκ', supportedConstantExchange_isIso A i i' v w sq,
      supported_kummer_boundary_pullback T N hN A hA hT i hI κ hκ
      t i' v w sq hI' κ' hκ'⟩
  · intro _
    obtain ⟨κ₀, hκ₀, _⟩ := supported_cartier_boundary_existsUnique T N hN
      (ULift.{u + 1} (ZMod N))
      (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
        (ZMod.natCast_self N)) hT i hI
    exact ⟨κ₀, hκ₀, supported_kummer_boundary_scalar T N hN A hA hT i hI κ hκ κ₀ hκ₀⟩

end

end AlgebraicGeometry.Etale
