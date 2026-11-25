/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.FiniteShiftedLineSquare
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
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange

/-! # Base change of one affine coordinate's coefficient descent

Source: vector integration, coefficient recursion in the overlap calculation.
(blueprint: lem-amb-affine-linear-line-descent-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000]
  DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] upperStar Functor.leftDerivedFunctor

private lemma square_paste (A : Type (u + 1)) [CommRing A]
    {U' U X' X Y' Y : Scheme.{u}}
    {t : U' ⟶ U} {g : X' ⟶ X} {f : Y' ⟶ Y}
    {r : U ⟶ X} {r' : U' ⟶ X'} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (sq₁ : CommSq t r' r g) (sq₂ : CommSq g p' p f)
    (v : U ⟶ Y) (v' : U' ⟶ Y') (hv : r ≫ p = v) (hv' : r' ≫ p' = v')
    (sq : CommSq t v' v f) (K : DerivedCategoryModule A Y) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₁).inv.app
        ((ordinaryFinitePullback A p).obj K) ≫
      (ordinaryFinitePullback A r').map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₂).inv.app K) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' p' v' hv'.symm).inv.app
        ((ordinaryFinitePullback A f).obj K) =
    (ordinaryFinitePullback A t).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r p v hv.symm).inv.app K) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app K := by
  have h₁ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    t r p (t ≫ r) v (t ≫ v) rfl hv.symm (by rw [← hv, Category.assoc]) K
  have h₂ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    r' g p (t ≫ r) (g ≫ p) (t ≫ v) sq₁.w rfl
      (by rw [← hv, ← Category.assoc]) K
  have h₃ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    r' p' f v' (g ≫ p) (t ≫ v) hv'.symm sq₂.w sq.w K
  apply (cancel_epi ((ordinaryFinitePullback A t).map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r p v hv.symm).hom.app K))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  symm
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    t v (t ≫ v) rfl).hom.app K)).mp
  simp only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.comp_obj, Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  erw [reassoc_of% h₁, Iso.hom_inv_id_app_assoc, ← reassoc_of% h₂,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% h₃, Iso.hom_inv_id_app, Category.comp_id]

private lemma tensor_square_transport
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory D'] [MonoidalCategory E]
    (P : C ⥤ D) (F : C ⥤ D') (G : D ⥤ E) (Q : D' ⥤ E)
    (s : P ⋙ G ≅ F ⋙ Q)
    {K L : C} {K' L' : D'} {X Y : D} {X' Y' : E}
    (a : X ⟶ P.obj K) (c : Y ⟶ P.obj L)
    (e : G.obj X ⟶ X') (l : G.obj Y ⟶ Y')
    (a' : X' ⟶ Q.obj K') (c' : Y' ⟶ Q.obj L')
    (b : F.obj K ⟶ K') (v : F.obj L ⟶ L')
    (δP : P.obj (K ⊗ L) ≅ P.obj K ⊗ P.obj L)
    (δF : F.obj (K ⊗ L) ≅ F.obj K ⊗ F.obj L)
    (δG : G.obj (X ⊗ Y) ≅ G.obj X ⊗ G.obj Y)
    (δG₀ : G.obj (P.obj K ⊗ P.obj L) ≅ G.obj (P.obj K) ⊗ G.obj (P.obj L))
    (δQ : Q.obj (K' ⊗ L') ≅ Q.obj K' ⊗ Q.obj L')
    (δQ₀ : Q.obj (F.obj K ⊗ F.obj L) ≅ Q.obj (F.obj K) ⊗ Q.obj (F.obj L))
    (ha : e ≫ a' = G.map a ≫ s.hom.app K ≫ Q.map b)
    (hc : l ≫ c' = G.map c ≫ s.hom.app L ≫ Q.map v)
    (hG : δG.hom ≫ (G.map a ⊗ₘ G.map c) = G.map (a ⊗ₘ c) ≫ δG₀.hom)
    (hQ : δQ₀.hom ≫ (Q.map b ⊗ₘ Q.map v) = Q.map (b ⊗ₘ v) ≫ δQ.hom)
    (hs : G.map δP.hom ≫ δG₀.hom ≫ (s.hom.app K ⊗ₘ s.hom.app L) =
      s.hom.app (K ⊗ L) ≫ Q.map δF.hom ≫ δQ₀.hom) :
    δG.hom ≫ ((e ≫ a') ⊗ₘ (l ≫ c')) ≫ δQ.inv =
      G.map ((a ⊗ₘ c) ≫ δP.inv) ≫ s.hom.app (K ⊗ L) ≫
        Q.map (δF.hom ≫ (b ⊗ₘ v)) := by
  rw [ha, hc]
  simp only [← tensorHom_comp_tensorHom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hG]
  have hs' : δG₀.hom ≫ (s.hom.app K ⊗ₘ s.hom.app L) =
      G.map δP.inv ≫ s.hom.app (K ⊗ L) ≫ Q.map δF.hom ≫ δQ₀.hom := by
    apply (cancel_epi (G.map δP.hom)).mp
    simpa only [Category.assoc, ← G.map_comp_assoc, Iso.hom_inv_id,
      G.map_id, Category.id_comp] using hs
  rw [reassoc_of% hs', reassoc_of% hQ]
  simp only [Iso.hom_inv_id, Category.comp_id]

private lemma chart_tensor_transport
    {C C' D D' : Type*}
    [Category C] [Category C'] [Category D] [Category D']
    [MonoidalCategory C] [MonoidalCategory C'] [MonoidalCategory D] [MonoidalCategory D']
    (J : C ⥤ D) (J' : C' ⥤ D') (G : C ⥤ C') (H : D ⥤ D')
    (s : J ⋙ H ≅ G ⋙ J')
    {K L : C} {K' L' : C'} {V W Z : D'}
    (b : G.obj K ≅ K') (c : G.obj L ≅ L')
    (a' : J'.obj K' ≅ V) (c' : J'.obj L' ≅ W)
    (δJ : J.obj (K ⊗ L) ≅ J.obj K ⊗ J.obj L)
    (δG : G.obj (K ⊗ L) ≅ G.obj K ⊗ G.obj L)
    (δH : H.obj (J.obj K ⊗ J.obj L) ≅ H.obj (J.obj K) ⊗ H.obj (J.obj L))
    (δJ₀ : J'.obj (G.obj K ⊗ G.obj L) ≅ J'.obj (G.obj K) ⊗ J'.obj (G.obj L))
    (δJ' : J'.obj (K' ⊗ L') ≅ J'.obj K' ⊗ J'.obj L') (v : V ⊗ W ⟶ Z)
    (hn : δJ₀.hom ≫ (J'.map b.hom ⊗ₘ J'.map c.hom) =
      J'.map (b.hom ⊗ₘ c.hom) ≫ δJ'.hom)
    (hs : H.map δJ.hom ≫ δH.hom ≫ (s.hom.app K ⊗ₘ s.hom.app L) =
      s.hom.app (K ⊗ L) ≫ J'.map δG.hom ≫ δJ₀.hom) :
    s.hom.app (K ⊗ L) ≫ J'.map (δG.hom ≫ (b.hom ⊗ₘ c.hom)) ≫
        δJ'.hom ≫ (a'.hom ⊗ₘ c'.hom) ≫ v =
      H.map δJ.hom ≫ δH.hom ≫
        ((s.hom.app K ≫ J'.map b.hom ≫ a'.hom) ⊗ₘ
          (s.hom.app L ≫ J'.map c.hom ≫ c'.hom)) ≫ v := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← reassoc_of% hs]
  simp only [tensorHom_comp_tensorHom_assoc]

private lemma tensor_mapIso_hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' L L' : DerivedCategoryModule A T} (e : K ≅ K') (c : L ≅ L') :
    (ordinaryFiniteTensorRightMapIso A T e c).hom = e.hom ⊗ₘ c.hom := by
  change e.hom ▷ L ≫ K' ◁ c.hom = e.hom ⊗ₘ c.hom
  rw [MonoidalCategory.tensorHom_def]

private lemma inverse_square
    {C : Type*} [Category C] {W X Y Z V : C}
    (s : W ≅ X) (p : X ≅ Y) (g : Y ≅ Z) (f : W ≅ V) (q : V ≅ Z)
    (h : s.hom ≫ p.hom ≫ g.hom = f.hom ≫ q.hom) :
    g.hom ≫ q.inv = p.inv ≫ s.inv ≫ f.hom := by
  apply (cancel_epi (s.hom ≫ p.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

private lemma square_tensor_inverse (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g p' p f)
    (K L : DerivedCategoryModule A Y) :
    (ordinaryFinitePullback A g).map (ordinaryFiniteTensorPullback A p K L).hom ≫
      (ordinaryFiniteTensorPullback A g ((ordinaryFinitePullback A p).obj K)
        ((ordinaryFinitePullback A p).obj L)).hom ≫
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app K ⊗ₘ
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app L) =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app (K ⊗ L) ≫
      (ordinaryFinitePullback A p').map (ordinaryFiniteTensorPullback A f K L).hom ≫
      (ordinaryFiniteTensorPullback A p' ((ordinaryFinitePullback A f).obj K)
        ((ordinaryFinitePullback A f).obj L)).hom := by
  have h := derivedSquareUpperStarIso_hom_tensor (ModuleCat.{u + 1} A) sq K L
  apply (cancel_epi ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
    (K ⊗ L))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  erw [← reassoc_of% h]
  simp only [tensorHom_comp_tensorHom, Iso.hom_inv_id_app]
  erw [id_tensorHom_id, Category.comp_id]
  rfl

private lemma tensor_descent_square (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g p' p f)
    {K L : DerivedCategoryModule A Y} {K' L' : DerivedCategoryModule A Y'}
    {M J : DerivedCategoryModule A X} {M' J' : DerivedCategoryModule A X'}
    (a : M ≅ (ordinaryFinitePullback A p).obj K)
    (c : J ≅ (ordinaryFinitePullback A p).obj L)
    (e : (ordinaryFinitePullback A g).obj M ≅ M')
    (l : (ordinaryFinitePullback A g).obj J ≅ J')
    (a' : M' ≅ (ordinaryFinitePullback A p').obj K')
    (c' : J' ≅ (ordinaryFinitePullback A p').obj L')
    (b : (ordinaryFinitePullback A f).obj K ≅ K')
    (v : (ordinaryFinitePullback A f).obj L ≅ L')
    (ha : e.hom ≫ a'.hom = (ordinaryFinitePullback A g).map a.hom ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app K ≫
        (ordinaryFinitePullback A p').map b.hom)
    (hc : l.hom ≫ c'.hom = (ordinaryFinitePullback A g).map c.hom ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app L ≫
        (ordinaryFinitePullback A p').map v.hom) :
    (ordinaryFiniteTensorPullback A g M J).hom ≫
      ((e.hom ≫ a'.hom) ⊗ₘ (l.hom ≫ c'.hom)) ≫
      (ordinaryFiniteTensorPullback A p' K' L').inv =
    (ordinaryFinitePullback A g).map
        ((a.hom ⊗ₘ c.hom) ≫ (ordinaryFiniteTensorPullback A p K L).inv) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app (K ⊗ L) ≫
      (ordinaryFinitePullback A p').map
        ((ordinaryFiniteTensorPullback A f K L).hom ≫ (b.hom ⊗ₘ v.hom)) := by
  exact tensor_square_transport
    (ordinaryFinitePullback A p) (ordinaryFinitePullback A f)
    (ordinaryFinitePullback A g) (ordinaryFinitePullback A p')
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm
    a.hom c.hom e.hom l.hom a'.hom c'.hom b.hom v.hom
    (ordinaryFiniteTensorPullback A p K L) (ordinaryFiniteTensorPullback A f K L)
    (ordinaryFiniteTensorPullback A g M J)
    (ordinaryFiniteTensorPullback A g ((ordinaryFinitePullback A p).obj K)
      ((ordinaryFinitePullback A p).obj L))
    (ordinaryFiniteTensorPullback A p' K' L')
    (ordinaryFiniteTensorPullback A p' ((ordinaryFinitePullback A f).obj K)
      ((ordinaryFinitePullback A f).obj L)) ha hc
    (leftDerivedUpperStarTensorComparison_naturality (ModuleCat.{u + 1} A) g a.hom c.hom)
    (leftDerivedUpperStarTensorComparison_naturality (ModuleCat.{u + 1} A) p' b.hom v.hom)
    (square_tensor_inverse A sq K L)

private lemma chart_square (A : Type (u + 1)) [CommRing A]
    {T S : Scheme.{u}} (f : T ⟶ S) :
    affineTraceOpenPullbackSquare A f =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (affineTraceChart_isPullback f).toCommSq).symm := by
  have hc {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
      (k k' : X ⟶ Z) (e : k = k') (hk : k = g ≫ h) (hk' : k' = g ≫ h) :
      eqToIso (congrArg (ordinaryFinitePullback A) e) ≪≫
          leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g h k' hk' =
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g h k hk := by
    subst e
    simp
  unfold affineTraceOpenPullbackSquare derivedSquareUpperStarIso
  rw [Iso.trans_symm]
  change _ = _ ≪≫ leftDerivedUpperStarComp _ _ _ _ _
  rw [hc]
  exact (affineTraceChart_isPullback f).w

private lemma line_descent_hom
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (K : DerivedCategoryModule A S) :
    (affineLinearLineDescent A N hA t S hS K).hom =
      (ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart S)
        ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K)
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)).hom ≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          (ProjectiveLine.affineChart S) (ProjectiveLine S ↘ S)
          (AffineSpace PUnit.{u + 1} S ↘ S) (ProjectiveLine.affineChart_over S).symm).inv.app
          K ⊗ₘ
        (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine.affineChart S)
          (affineTraceProjectiveInvertible N S hS)).hom ≫
        (ordinaryFiniteShiftedLinePullback A N hA t
          (AffineSpace PUnit.{u + 1} S ↘ S) hS).inv) ≫
      (ordinaryFiniteTensorPullback A (AffineSpace PUnit.{u + 1} S ↘ S) K
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).inv := by
  simp only [affineLinearLineDescent, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    tensor_mapIso_hom]

private lemma tensor_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K K' L L' : DerivedCategoryModule A Y} (e : K ⟶ K') (c : L ⟶ L') :
    (ordinaryFiniteTensorPullback A f K L).hom ≫
      ((ordinaryFinitePullback A f).map e ⊗ₘ (ordinaryFinitePullback A f).map c) =
    (ordinaryFinitePullback A f).map (e ⊗ₘ c) ≫
      (ordinaryFiniteTensorPullback A f K' L').hom := by
  exact leftDerivedUpperStarTensorComparison_naturality (ModuleCat.{u + 1} A) f e c

attribute [local irreducible] affineLinearLineDescent ordinaryFiniteTensorPullback
  ordinaryFiniteTensorRightMapIso

/-- The single-coordinate descent intertwines its right base-change comparison with
inverse image of a tensor with the shifted Tate line, naturally in its input.
Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration.proof.md,
coefficient comparison in the overlap calculation.
(blueprint: lem-amb-affine-linear-line-descent-base-change).

Proof: expand the one-coordinate right comparison as the affine-chart square
comparison followed by pullback of the projective-line right comparison. Expand
line descent as tensor pullback along the chart, inverse-image composition from
chart followed by projective projection to affine projection, normalized shifted
line transport, and inverse tensor pullback along the affine projection. Naturality
of tensor pullback moves the two projective-line comparison factors through the
chart tensor comparison. Monoidality of the chart square identifies its tensor
comparison with the comparisons of both factors. Associativity of inverse-image
composition pastes the projective projection square with the chart square; the
chart-over-projection identity identifies their composite with the affine square.
For the line factor, apply the normalized shifted-line square law first to the
chart square and then to the affine projection square. The intermediate line
comparisons cancel with their inverses, leaving inverse image of the base's
normalized line comparison. Apply tensor naturality to the arbitrary input
isomorphism and cancel the remaining tensor comparison. The resulting expression
is the right-hand side. All inputs are unbounded derived objects; no finiteness,
Noetherian hypothesis, positive rank or nonempty scheme is used. -/
theorem affineLinearLineDescent_baseChange
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {T S : Scheme.{u}} (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hT : IsUnit (N : Γ(T, ⊤)))
    (K : DerivedCategoryModule A S) (K' : DerivedCategoryModule A T)
    (e : (ordinaryFinitePullback A f).obj K ≅ K') :
    affineTraceLineRightBaseChange A N hA t f (affineTraceProjectiveInvertible N S hS) K ≪≫
      (affineTraceLineRight A N hA T).mapIso e ≪≫
      affineLinearLineDescent A N hA t T hT K' =
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).mapIso
        (affineLinearLineDescent A N hA t S hS K) ≪≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f).toCommSq).symm.app
          ((derivedTensorRight (ModuleCat.{u + 1} A) S
            ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj K) ≪≫
      (ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).mapIso
        (ordinaryFiniteTensorPullback A f K ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧) ≪≫
          ordinaryFiniteTensorRightMapIso A T e
            (ordinaryFiniteShiftedLinePullback A N hA t f hS)) := by
  let j := ProjectiveLine.affineChart S
  let j' := ProjectiveLine.affineChart T
  let q := ProjectiveLine S ↘ S
  let q' := ProjectiveLine T ↘ T
  let p := AffineSpace PUnit.{u + 1} S ↘ S
  let p' := AffineSpace PUnit.{u + 1} T ↘ T
  let g := ProjectiveSpace.map (ULift.{u} (Fin 2)) f
  let h := AffineSpace.map PUnit.{u + 1} f
  let L := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧
  let L' := (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧
  let LP := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  let LP' := (ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧
  let sqj := (affineTraceChart_isPullback f).toCommSq
  let sqq := (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq
  let sqp := (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f).toCommSq
  let a := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j q p
    (ProjectiveLine.affineChart_over S).symm).symm.app K
  let a' := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j' q' p'
    (ProjectiveLine.affineChart_over T).symm).symm.app K'
  let cj := ordinaryFiniteShiftedLinePullback A N hA t j
    (affineTraceProjectiveInvertible N S hS)
  let cj' := ordinaryFiniteShiftedLinePullback A N hA t j'
    (affineTraceProjectiveInvertible N T hT)
  let cp := ordinaryFiniteShiftedLinePullback A N hA t p hS
  let cp' := ordinaryFiniteShiftedLinePullback A N hA t p' hT
  let cg := ordinaryFiniteShiftedLinePullback A N hA t g
    (affineTraceProjectiveInvertible N S hS)
  let ch := ordinaryFiniteShiftedLinePullback A N hA t h
    (affineTracePullbackInvertible N p hS)
  let cf := ordinaryFiniteShiftedLinePullback A N hA t f hS
  let c := cj ≪≫ cp.symm
  let b₁ := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqq).symm.app K ≪≫
    (ordinaryFinitePullback A q').mapIso e
  let e₁ := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqj).symm.app
      ((ordinaryFinitePullback A q).obj K) ≪≫
    (ordinaryFinitePullback A j').mapIso b₁ ≪≫ a'
  let l₁ := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqj).symm.app LP ≪≫
    (ordinaryFinitePullback A j').mapIso cg ≪≫ cj' ≪≫ cp'.symm
  have ha : e₁.hom = (ordinaryFinitePullback A h).map a.hom ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app K ≫
        (ordinaryFinitePullback A p').map e.hom := by
    as_aux_lemma =>
      have hp := square_paste A sqj sqq p p'
        (ProjectiveLine.affineChart_over S) (ProjectiveLine.affineChart_over T) sqp K
      have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j' q' p'
        (ProjectiveLine.affineChart_over T).symm).inv.naturality e.hom
      simp only [Functor.comp_map] at hn
      simp only [e₁, b₁, a', a, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc]
      erw [hn, reassoc_of% hp]
      rfl
  have hc : l₁.hom = (ordinaryFinitePullback A h).map c.hom ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app L ≫
        (ordinaryFinitePullback A p').map cf.hom := by
    as_aux_lemma =>
      have hj := ordinaryFiniteShiftedLinePullback_square A N hA t sqj
        (affineTraceProjectiveInvertible N S hS) (affineTraceProjectiveInvertible N T hT)
        (affineTracePullbackInvertible N p hS)
      have hh : (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqj).inv.app LP ≫
          (ordinaryFinitePullback A j').map cg.hom ≫ cj'.hom =
          (ordinaryFinitePullback A h).map cj.hom ≫ ch.hom := by
        apply (cancel_epi ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqj).hom.app
          LP)).mp
        simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hj.symm
      have hp := inverse_square
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).app L)
        ((ordinaryFinitePullback A h).mapIso cp) ch
        ((ordinaryFinitePullback A p').mapIso cf) cp'
        (ordinaryFiniteShiftedLinePullback_square A N hA t sqp hS hT
          (affineTracePullbackInvertible N p hS))
      simp only [l₁, c, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
        Functor.map_comp, Category.assoc]
      erw [reassoc_of% hh, hp]
      rfl
  have ht : (ordinaryFiniteTensorPullback A h
        ((ordinaryFinitePullback A j).obj ((ordinaryFinitePullback A q).obj K))
        ((ordinaryFinitePullback A j).obj LP)).hom ≫
      (e₁.hom ⊗ₘ l₁.hom) ≫ (ordinaryFiniteTensorPullback A p' K' L').inv =
    (ordinaryFinitePullback A h).map
        ((a.hom ⊗ₘ c.hom) ≫ (ordinaryFiniteTensorPullback A p K L).inv) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app (K ⊗ L) ≫
      (ordinaryFinitePullback A p').map
        ((ordinaryFiniteTensorPullback A f K L).hom ≫ (e.hom ⊗ₘ cf.hom)) := by
    as_aux_lemma =>
      have hh := tensor_descent_square A sqp a c e₁ l₁ (Iso.refl _) (Iso.refl _) e cf
        (by simpa only [Iso.refl_hom, Category.comp_id] using ha)
        (by simpa only [Iso.refl_hom, Category.comp_id] using hc)
      simp only [Iso.refl_hom, Category.comp_id] at hh
      dsimp only [h, g, p, p', L, L', LP, LP', j, j', q, q',
        ordinaryFinitePullback, Functor.comp_obj] at hh ⊢
      exact hh
  have hj := square_tensor_inverse A sqj ((ordinaryFinitePullback A q).obj K) LP
  have hn := tensor_naturality A j' b₁.hom cg.hom
  have hb : (ordinaryFiniteP1RightBaseChange A N hA t f
        (affineTraceProjectiveInvertible N S hS) K).hom ≫
      (ordinaryFiniteP1Right A N hA T).map e.hom =
      (ordinaryFiniteTensorPullback A g ((ordinaryFinitePullback A q).obj K) LP).hom ≫
        (b₁.hom ⊗ₘ cg.hom) := by
    as_aux_lemma =>
      simp only [ordinaryFiniteP1RightBaseChange, ordinaryFiniteTwistedPullbackComparison,
        Iso.trans_hom, tensor_mapIso_hom, Category.assoc]
      change _ ≫ (_ ⊗ₘ cg.hom) ≫
        ((ordinaryFinitePullback A q').map e.hom ▷ LP') = _
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
      erw [Category.comp_id]
      rfl
  have hr : (affineTraceLineRightBaseChange A N hA t f
        (affineTraceProjectiveInvertible N S hS) K).hom ≫
      (affineTraceLineRight A N hA T).map e.hom =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqj).inv.app
        (((ordinaryFinitePullback A q).obj K) ⊗ LP) ≫
      (ordinaryFinitePullback A j').map
        ((ordinaryFiniteTensorPullback A g ((ordinaryFinitePullback A q).obj K) LP).hom ≫
          (b₁.hom ⊗ₘ cg.hom)) := by
    as_aux_lemma =>
      simp only [affineTraceLineRightBaseChange, affineTraceCompositeRightSquareIso,
        affineTraceRightSquareIso_eq, chart_square, Iso.trans_hom, Iso.symm_hom,
        Iso.app_hom, Functor.mapIso_hom, Category.assoc]
      change _ ≫ (ordinaryFinitePullback A j').map
        (ordinaryFiniteP1RightBaseChange A N hA t f
          (affineTraceProjectiveInvertible N S hS) K).hom ≫
        (ordinaryFinitePullback A j').map ((ordinaryFiniteP1Right A N hA T).map e.hom) = _
      rw [← Functor.map_comp, hb]
      rfl
  as_aux_lemma =>
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    erw [reassoc_of% hr]
    rw [line_descent_hom, line_descent_hom]
    simp only [Iso.symm_hom, Iso.app_hom, tensor_mapIso_hom]
    change
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqj).inv.app
          (((ordinaryFinitePullback A q).obj K) ⊗ LP) ≫
        (ordinaryFinitePullback A j').map
          ((ordinaryFiniteTensorPullback A g ((ordinaryFinitePullback A q).obj K) LP).hom ≫
            (b₁.hom ⊗ₘ cg.hom)) ≫
        (ordinaryFiniteTensorPullback A j' ((ordinaryFinitePullback A q').obj K') LP').hom ≫
        (a'.hom ⊗ₘ (cj' ≪≫ cp'.symm).hom) ≫
        (ordinaryFiniteTensorPullback A p' K' L').inv =
      (ordinaryFinitePullback A h).map
          ((ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K) LP).hom ≫
            (a.hom ⊗ₘ c.hom) ≫ (ordinaryFiniteTensorPullback A p K L).inv) ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqp).inv.app (K ⊗ L) ≫
        (ordinaryFinitePullback A p').map
          ((ordinaryFiniteTensorPullback A f K L).hom ≫ (e.hom ⊗ₘ cf.hom))
    have hcalc := chart_tensor_transport
      (ordinaryFinitePullback A j) (ordinaryFinitePullback A j')
      (ordinaryFinitePullback A g) (ordinaryFinitePullback A h)
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqj).symm
      b₁ cg a' (cj' ≪≫ cp'.symm)
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K) LP)
      (ordinaryFiniteTensorPullback A g ((ordinaryFinitePullback A q).obj K) LP)
      (ordinaryFiniteTensorPullback A h
        ((ordinaryFinitePullback A j).obj ((ordinaryFinitePullback A q).obj K))
        ((ordinaryFinitePullback A j).obj LP))
      (ordinaryFiniteTensorPullback A j'
        ((ordinaryFinitePullback A g).obj ((ordinaryFinitePullback A q).obj K))
        ((ordinaryFinitePullback A g).obj LP))
      (ordinaryFiniteTensorPullback A j' ((ordinaryFinitePullback A q').obj K') LP')
      (ordinaryFiniteTensorPullback A p' K' L').inv hn hj
    change _ = (ordinaryFinitePullback A h).map
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K) LP).hom ≫
        (ordinaryFiniteTensorPullback A h
          ((ordinaryFinitePullback A j).obj ((ordinaryFinitePullback A q).obj K))
          ((ordinaryFinitePullback A j).obj LP)).hom ≫
        (e₁.hom ⊗ₘ l₁.hom) ≫ (ordinaryFiniteTensorPullback A p' K' L').inv at hcalc
    have hfinal := congrArg (fun z ↦ (ordinaryFinitePullback A h).map
      (ordinaryFiniteTensorPullback A j ((ordinaryFinitePullback A q).obj K) LP).hom ≫ z) ht
    have hh := hcalc.trans hfinal
    simp only [Functor.map_comp, Category.assoc, Iso.symm_hom] at hh ⊢
    dsimp only [h, g, p, p', L, L', LP, LP', j, j', q, q',
      ordinaryFinitePullback, Functor.comp_obj] at hh ⊢
    exact hh

end AlgebraicGeometry.Etale
