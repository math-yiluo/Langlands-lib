/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
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
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearLineDescentBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange

/-! # Affine tower coefficient base-change recursion

(blueprint: lem-amb-vector-integration-restricted-chart-coefficient-core).
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

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

private lemma square_eq (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g p' p f)
    (m : X' ⟶ Y) (hm : m = g ≫ p) :
    derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' f m (hm.trans sq.w)).symm ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g p m hm := by
  subst m
  rfl

private lemma zero_square (A : Type (u + 1)) [CommRing A]
    {T S : Scheme.{u}} (f : T ⟶ S) (K : DerivedCategoryModule A S)
    (L : DerivedCategoryModule A T) (e : (ordinaryFinitePullback A f).obj K ≅ L) :
    e =
      (ordinaryFinitePullback A f).mapIso ((affineLinearPullbackId A S).app K).symm ≪≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.id_vert f).toCommSq).symm.app K ≪≫
      (ordinaryFinitePullback A (𝟙 T)).mapIso e ≪≫
      (affineLinearPullbackId A T).app L := by
  apply Iso.ext
  rw [square_eq A (IsPullback.id_vert f).toCommSq f (Category.comp_id f).symm]
  simp only [pullback_id_eq, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapIso_hom, Category.assoc]
  have hr := leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) f K
  have hl := leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) f K
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.naturality e.hom
  simp only [Functor.id_map] at hn
  dsimp only [ordinaryFinitePullback] at *
  erw [hn]
  have hli :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 T) f f
        (Category.id_comp f).symm).inv.app K =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app
          ((ordinaryFinitePullback A f).obj K) := by
    apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (𝟙 T) f f (Category.id_comp f).symm).hom.app K)).mp
    simpa only [ordinaryFinitePullback, Iso.hom_inv_id_app] using hl.symm
  erw [← hli, Iso.hom_inv_id_app_assoc]
  have hri :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f (𝟙 S) f
        (Category.comp_id f).symm).hom.app K =
        (ordinaryFinitePullback A f).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app K) := by
    apply (cancel_mono ((ordinaryFinitePullback A f).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app K))).mp
    simpa only [ordinaryFinitePullback, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Functor.id_obj] using hr
  erw [← hri, Iso.hom_inv_id_app_assoc]

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

private lemma descent_succ_iso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearCoefficientDescent A N hA t S hS (d + 1) =
      affineLinearCoefficientDescentStep A N hA t S hS d
        (affineLinearCoefficientDescent A N hA t S hS d) := by
  rfl

private lemma descent_step_hom (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (e : (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (affineLinearBaseCoefficient A N hA S d)) :
    (affineLinearCoefficientDescentStep A N hA t S hS d e).hom =
      (affineLinearLineDescent A N hA t (affineTraceTower S d)
        (affineTraceInvertible N S hS d)
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))).hom ≫
      (ordinaryFinitePullback A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).map
        ((e.hom ⊗ₘ
          (ordinaryFiniteShiftedLinePullback A N hA t (affineTraceProjection S d) hS).inv) ≫
        (ordinaryFiniteTensorPullback A (affineTraceProjection S d)
          (affineLinearBaseCoefficient A N hA S d)
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).inv) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d)).inv.app (affineLinearBaseCoefficient A N hA S (d + 1)) := by
  simp only [affineLinearCoefficientDescentStep, Iso.trans_hom, Functor.mapIso_hom,
    tensor_mapIso_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp]

private lemma base_succ_iso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {T S : Scheme.{u}} (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    vectorIntegrationBaseCoefficientPullback A N hA t f hS (d + 1) =
      ordinaryFiniteTensorPullback A f (affineLinearBaseCoefficient A N hA S d)
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧) ≪≫
      ordinaryFiniteTensorRightMapIso A T
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS d)
        (ordinaryFiniteShiftedLinePullback A N hA t f hS) := by
  rfl

attribute [local irreducible] affineLinearCoefficientDescent
  affineLinearCoefficientDescentStep

-- Keep the one-coordinate functors abstract while checking the recursion formula.
attribute [local irreducible] ordinaryFiniteP1Right ordinaryFiniteTwistedPullback
  derivedTensorRight affineLinearLineDescent affineTraceRightBaseChange
  ordinaryFiniteTensorPullback ordinaryFiniteTensorRightMapIso

private lemma right_unit_succ_hom
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {T S : Scheme.{u}} (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceRightBaseChange A N hA t f hS (d + 1) (ordinaryFiniteUnit A S)).hom ≫
      (affineTraceRight A N hA T (d + 1)).map (ordinaryFiniteUnitPullback A f).hom =
    (affineTraceLineRightBaseChange A N hA t (affineTraceMap f d)
      (affineTraceProjectiveInvertible N (affineTraceTower S d)
        (affineTraceInvertible N S hS d))
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))).hom ≫
      (affineTraceLineRight A N hA (affineTraceTower T d)).map
        ((affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S)).hom ≫
          (affineTraceRight A N hA T d).map (ordinaryFiniteUnitPullback A f).hom) := by
  simp only [affineTraceRightBaseChange, affineTraceRightExchangeTower,
    Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, ← Category.assoc]
  rfl

attribute [local irreducible] vectorIntegrationBaseCoefficientPullback

-- The remaining tensor calculation uses the object formula of this functor.
attribute [local semireducible] derivedTensorRight

private lemma tower_square
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {T S : Scheme.{u}} (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S) ≪≫
      (affineTraceRight A N hA T d).mapIso (ordinaryFiniteUnitPullback A f) ≪≫
      affineLinearCoefficientDescent A N hA t T hT d =
    (ordinaryFinitePullback A (affineTraceMap f d)).mapIso
        (affineLinearCoefficientDescent A N hA t S hS d) ≪≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (affineTraceMap_isPullback f d).toCommSq).symm.app
          (affineLinearBaseCoefficient A N hA S d) ≪≫
      (ordinaryFinitePullback A (affineTraceProjection T d)).mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS d) := by
  induction d with
  | zero =>
    have h := congrArg (fun i ↦ i.hom ≫
      ((affineLinearPullbackId A T).app (ordinaryFiniteUnit A T)).inv)
      (zero_square A f (ordinaryFiniteUnit A S) (ordinaryFiniteUnit A T)
        (ordinaryFiniteUnitPullback A f))
    apply Iso.ext
    simpa only [affineTraceRightBaseChange, affineTraceRightExchangeTower,
      affineTraceRight, affineTraceRightTower, affineTraceMap, affineTraceProjection,
      affineLinearCoefficientDescent, vectorIntegrationBaseCoefficientPullback,
      Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, Functor.id_map,
      Category.id_comp, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id,
      Category.comp_id, Nat.rec_zero,
      affineLinearBaseCoefficient] using h
  | succ d ih =>
    let X := (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)
    let X' := (affineTraceRight A N hA T d).obj (ordinaryFiniteUnit A T)
    let p := affineTraceProjection S d
    let p' := affineTraceProjection T d
    let g := affineTraceMap f d
    let r := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
    let r' := AffineSpace PUnit.{u + 1} (affineTraceTower T d) ↘ affineTraceTower T d
    let B := affineLinearBaseCoefficient A N hA S d
    let B' := affineLinearBaseCoefficient A N hA T d
    let L := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧
    let L' := (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧
    let a := affineLinearCoefficientDescent A N hA t S hS d
    let a' := affineLinearCoefficientDescent A N hA t T hT d
    let b := vectorIntegrationBaseCoefficientPullback A N hA t f hS d
    let cp := ordinaryFiniteShiftedLinePullback A N hA t p hS
    let cp' := ordinaryFiniteShiftedLinePullback A N hA t p' hT
    let cg := ordinaryFiniteShiftedLinePullback A N hA t g (affineTraceInvertible N S hS d)
    let cf := ordinaryFiniteShiftedLinePullback A N hA t f hS
    let e := affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S) ≪≫
      (affineTraceRight A N hA T d).mapIso (ordinaryFiniteUnitPullback A f)
    let sq := (affineTraceMap_isPullback f d).toCommSq
    let sqr := (AffineSpace.isPullback_map (n := PUnit.{u + 1}) g).toCommSq
    let α := (a.hom ⊗ₘ cp.inv) ≫ (ordinaryFiniteTensorPullback A p B L).inv
    let α' := (a'.hom ⊗ₘ cp'.inv) ≫ (ordinaryFiniteTensorPullback A p' B' L').inv
    let β := (ordinaryFiniteTensorPullback A f B L).hom ≫ (b.hom ⊗ₘ cf.hom)
    let z := (ordinaryFiniteTensorPullback A g X
      ((ordinaryFiniteLine A N hA (affineTraceTower S d))⟦(2 : ℤ)⟧)).hom ≫
        (e.hom ⊗ₘ cg.hom)
    have ha : e.hom ≫ a'.hom = (ordinaryFinitePullback A g).map a.hom ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app B ≫
          (ordinaryFinitePullback A p').map b.hom := by
      dsimp only [e, a, a', g, B, sq, p', b]
      simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
        Category.assoc] using congrArg Iso.hom ih
    have hc : cg.hom ≫ cp'.inv = (ordinaryFinitePullback A g).map cp.inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app L ≫
          (ordinaryFinitePullback A p').map cf.hom := by
      exact inverse_square
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).app L)
        ((ordinaryFinitePullback A g).mapIso cp) cg
        ((ordinaryFinitePullback A p').mapIso cf) cp'
        (ordinaryFiniteShiftedLinePullback_square A N hA t sq hS hT
          (affineTraceInvertible N S hS d))
    have ht : z ≫ α' = (ordinaryFinitePullback A g).map α ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app (B ⊗ L) ≫
          (ordinaryFinitePullback A p').map β := by
      have hh := tensor_descent_square A sq a cp.symm e cg a' cp'.symm b cf ha hc
      simpa only [z, α, α', β, Iso.symm_hom, Category.assoc,
        tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom] using hh
    have hl := congrArg Iso.hom (affineLinearLineDescent_baseChange A N hA t g
      (affineTraceInvertible N S hS d) (affineTraceInvertible N T hT d) X X' e)
    have hn := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqr).inv.naturality α
    have hm := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' p').inv.naturality β
    have hp := square_paste A sqr sq (r ≫ p) (r' ≫ p') rfl rfl
      (affineTraceMap_isPullback f (d + 1)).toCommSq
      (B ⊗ L)
    simp only [Functor.comp_map] at hn hm
    simp only [Iso.trans_hom, Functor.mapIso_hom, tensor_mapIso_hom,
      Iso.symm_hom, Iso.app_hom] at hl
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom, descent_succ_iso, descent_step_hom,
      base_succ_iso, tensor_mapIso_hom, Iso.symm_hom, Iso.app_hom]
    erw [reassoc_of% (right_unit_succ_hom A N hA t f hS d)]
    change
      (affineTraceLineRightBaseChange A N hA t g
          (affineTraceProjectiveInvertible N (affineTraceTower S d)
            (affineTraceInvertible N S hS d)) X).hom ≫
        (affineTraceLineRight A N hA (affineTraceTower T d)).map e.hom ≫
        (affineLinearLineDescent A N hA t (affineTraceTower T d)
          (affineTraceInvertible N T hT d) X').hom ≫
        (ordinaryFinitePullback A r').map α' ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' p').inv.app (B' ⊗ L') =
      (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} g)).map
        ((affineLinearLineDescent A N hA t (affineTraceTower S d)
          (affineTraceInvertible N S hS d) X).hom ≫
        (ordinaryFinitePullback A r).map α ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r p).inv.app (B ⊗ L)) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (affineTraceMap_isPullback f (d + 1)).toCommSq).inv.app (B ⊗ L) ≫
      (ordinaryFinitePullback A (r' ≫ p')).map β
    erw [reassoc_of% hl]
    change _ ≫ _ ≫ (ordinaryFinitePullback A r').map z ≫
      (ordinaryFinitePullback A r').map α' ≫ _ = _
    erw [← Functor.map_comp_assoc, ht]
    simp only [Functor.map_comp, Category.assoc]
    erw [← reassoc_of% hn, hm, reassoc_of% hp]
    rfl

/-- The affine-tower right base-change comparison at the constant unit is the
canonical descent comparison for the ordered Tate coefficient. This is the
coefficient recursion part of the restricted-chart calculation; it has no
vector bundle or frame. The proof is by induction on the ordered tower length,
using derived inverse-image identity coherence at zero, one-coordinate descent
naturality, and monoidal shifted-line comparison at a successor.
(blueprint: lem-amb-vector-integration-restricted-chart-coefficient-core). -/
theorem affineTraceRightBaseChange_unit_coefficient
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {T S : Scheme.{u}} (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S) ≪≫
      (affineTraceRight A N hA T d).mapIso (ordinaryFiniteUnitPullback A f) =
    (ordinaryFinitePullback A (affineTraceMap f d)).mapIso
        (affineLinearCoefficientDescent A N hA t S hS d) ≪≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (affineTraceMap_isPullback f d).toCommSq).symm.app
          (affineLinearBaseCoefficient A N hA S d) ≪≫
      (ordinaryFinitePullback A (affineTraceProjection T d)).mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS d) ≪≫
      (affineLinearCoefficientDescent A N hA t T hT d).symm := by
  apply Iso.ext
  apply (cancel_mono (affineLinearCoefficientDescent A N hA t T hT d).hom).mp
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using
    congrArg Iso.hom (tower_square A N hA t f hS hT d)

end AlgebraicGeometry.Etale
