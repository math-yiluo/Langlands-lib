/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedPairingPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAssociativity
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackCounit
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
import WeilConjectures.CategoryTheory.FlatPairingAssociativityAssembly
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.FlatPairingPullbackAssembly
import WeilConjectures.AlgebraicGeometry.DerivedPairingOppositeShiftsPullback
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPairing
import WeilConjectures.AlgebraicGeometry.FiniteTwistFlatEvaluationPullback
import WeilConjectures.AlgebraicGeometry.FlatSinglePairingSymmetricPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDerivedRightUnitPullback
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
import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedFactorComparisons
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.Tensor.TensorProjectionAdjunct

/-! # Cancelling the positive twist in the projective-line splitting
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

private theorem descIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} {X' Y' Z' : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) [IsIso (biprod.desc a b)]
    (e : F.obj X ≅ X') (e' : F.obj Y ≅ Y') (v : F.obj Z ≅ Z') :
    IsIso (biprod.desc (e.inv ≫ F.map a ≫ v.hom) (e'.inv ≫ F.map b ≫ v.hom)) := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let q := biprod.mapIso e.symm e'.symm ≪≫ (Functor.mapBiprod F X Y).symm ≪≫
    F.mapIso (asIso (biprod.desc a b)) ≪≫ v
  have h : q.hom = biprod.desc (e.inv ≫ F.map a ≫ v.hom)
      (e'.inv ≫ F.map b ≫ v.hom) := by
    apply biprod.hom_ext' <;>
      simp [q, ← Functor.map_comp_assoc]
  rw [← h]
  infer_instance

private theorem untwistIsIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (P : C ⥤ C ⥤ C) (Q : D ⥤ D ⥤ D) (K L U : C) (E V : D)
    [(P.obj K).Additive]
    (delta : ∀ M, F.obj ((P.obj K).obj M) ⟶ (Q.obj (F.obj K)).obj (F.obj M))
    (proj : (P.obj K).obj (G.obj E) ⟶ G.obj ((Q.obj (F.obj K)).obj E)) [IsIso proj]
    (hproj : ∀ (M : C) (a : M ⟶ G.obj E),
      (adj.homEquiv _ _).symm ((P.obj K).map a ≫ proj) =
        delta M ≫ (Q.obj (F.obj K)).map ((adj.homEquiv _ _).symm a))
    (e : (P.obj K).obj L ≅ U) (r : (P.obj K).obj U ≅ K)
    (u : F.obj U ≅ V) (l : F.obj L ≅ E)
    (w : (Q.obj (F.obj K)).obj E ≅ V)
    (r' : (Q.obj (F.obj K)).obj V ≅ F.obj K)
    (he : F.map e.hom ≫ u.hom =
      delta L ≫ (Q.obj (F.obj K)).map l.hom ≫ w.hom)
    (hr : F.map r.inv ≫ delta U ≫ (Q.obj (F.obj K)).map u.hom = r'.inv)
    (c : V ⟶ E)
    (hb : IsIso (biprod.desc (adj.homEquiv _ _ l.hom)
      (adj.homEquiv _ _ (u.hom ≫ c)))) :
    IsIso (biprod.desc (adj.homEquiv _ _ u.hom)
      (adj.homEquiv _ _ (r'.inv ≫ (Q.obj (F.obj K)).map c ≫ w.hom))) := by
  let a := adj.homEquiv _ _ l.hom
  let b := adj.homEquiv _ _ (u.hom ≫ c)
  let v := asIso proj ≪≫ G.mapIso w
  have trans (M : C) (z : M ⟶ G.obj E) :
      (adj.homEquiv _ _).symm ((P.obj K).map z ≫ v.hom) =
        delta M ≫ (Q.obj (F.obj K)).map ((adj.homEquiv _ _).symm z) ≫ w.hom := by
    dsimp only [v, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm, hproj]
    simp only [Category.assoc]
  have ha : e.inv ≫ (P.obj K).map a ≫ v.hom = adj.homEquiv _ _ u.hom := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm, trans]
    simp only [a, Equiv.symm_apply_apply]
    rw [← he]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  have hb' : r.inv ≫ (P.obj K).map b ≫ v.hom =
      adj.homEquiv _ _ (r'.inv ≫ (Q.obj (F.obj K)).map c ≫ w.hom) := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm, trans]
    simp only [b, Equiv.symm_apply_apply, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hr]
  have := descIso (P.obj K) a b e r v
  rw [ha, hb'] at this
  exact this

private theorem evaluation_isIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    IsIso (p1DecompositionEvaluation A N hN hA T hT) := by
  have hv : IsIso ((ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
      (ordinaryFiniteConstant A T)) := by
    change IsIso ((ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
      (Scheme.finiteEtaleTateSheaf A N T hA 0))
    rw [← p1DecompositionSheafProduct_hom A N hN hA T hT]
    infer_instance
  unfold p1DecompositionEvaluation p1DecompositionDegreeZeroEvaluation
  infer_instance

/-- Tensoring the normalized positive-twist splitting with the inverse line gives
exactly the unit and Chern-evaluation splitting. No Noetherian hypothesis is needed:
the source library's finite-coefficient proper projection formula is unbounded and
holds over every base. -/
theorem isIso_p1DecompositionMap_of_twisted
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hb : IsIso (biprod.desc (ordinaryFiniteP1Unit A N hA t S hS)
      (ordinaryFiniteP1ChernPushforward A N hA S c))) :
    IsIso (p1DecompositionMap A N hN hA S hS c) := by
  let q := ProjectiveLine S ↘ S
  let K := p1DecompositionTwist A N hA S (-1) (-2)
  let L := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧
  let E := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  have : IsProper q := ProjectiveSpace.instIsProper (ULift.{u} (Fin 2)) S
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A q
  have hp : IsIso (ordinaryFiniteProjection A q E K) := by
    unfold ordinaryFiniteProjection
    infer_instance
  have := evaluation_isIso A N hN hA S hS
  have := evaluation_isIso A N hN hA (ProjectiveLine S)
    ((map_natCast q.appTop.hom N) ▸ hS.map q.appTop.hom)
  let w : ((ordinaryFiniteTensor A (ProjectiveLine S)).obj
      ((ordinaryFinitePullback A q).obj K)).obj E ≅
        ordinaryFiniteUnit A (ProjectiveLine S) :=
    ((ordinaryFiniteTensor A (ProjectiveLine S)).mapIso
      (p1DecompositionTwistPullback A N hN hA q hS (-1) (-2))).app E ≪≫
      asIso (p1DecompositionEvaluation A N hN hA (ProjectiveLine S)
        ((map_natCast q.appTop.hom N) ▸ hS.map q.appTop.hom))
  obtain ⟨he, hr⟩ := finiteTwistDerivedEvaluation_pullback A N hN hA t q hS
  have : ((ordinaryFiniteTensor A S).obj K).Additive :=
    additive_derivedTensor_obj K
  have h := untwistIsIso (ordinaryFinitePullback A q) (ordinaryFinitePushforward A q)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (ordinaryFiniteTensor A S) (ordinaryFiniteTensor A (ProjectiveLine S)) K L
    (ordinaryFiniteUnit A S) E (ordinaryFiniteUnit A (ProjectiveLine S))
    (fun M => ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) q).app K).app M)
    (ordinaryFiniteProjection A q E K)
    (fun M a => tensorProjectionAdjunct A q K M E a)
    (asIso (p1DecompositionEvaluation A N hN hA S hS))
    (derivedTensorSingleUnitIso K) (ordinaryFiniteUnitPullback A q)
    (ordinaryFiniteShiftedLinePullback A N hA t q hS) w
    (derivedTensorSingleUnitIso ((ordinaryFinitePullback A q).obj K)) he (hr K) c
    (by simpa only [ordinaryFiniteP1Unit, ordinaryFiniteP1ChernPushforward,
      Adjunction.homEquiv_apply, K, L, E, q, Functor.id_obj,
      ordinaryFinitePushforward] using hb)
  simpa only [p1DecompositionMap, p1DecompositionUnit, p1DecompositionChernAdjoint,
    p1DecompositionTensorAdjoint, w, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Category.assoc, K, L, E, q,
    ordinaryFinitePushforward,
    ordinaryFinitePullback, ordinaryFiniteTensor] using h

end AlgebraicGeometry.Etale
