/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierSourceComparison
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
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
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import all WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import all WeilConjectures.CategoryTheory.FlatScalarUnit
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import all WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Unique
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import all WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.SixFunctors.Finite.Stalk
import all Mathlib.CategoryTheory.Sites.Adjunction
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierScalarUnitOfUniversal
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-! # Normalized coefficient units for Cartier source and target objects -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] comparisonUpperStar
open Scheme
open scoped CategoryTheory.Functor
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

private noncomputable def normalizedConstantMap {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (D : Scheme.{u}) :
    geoCartierConstant R D ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant S D) :=
  let hT : IsTerminal (Scheme.ProEt.mk (𝟙 D)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  ((constantSheafAdj (Scheme.ProEt.topology D) (ModuleCat.{u + 1} R) hT).homEquiv _ _).symm
    (ModuleCat.ofHom
      (Y := ((Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj
        (geoCartierConstant S D)).obj.obj
          (op (Scheme.ProEt.mk (𝟙 D))))
      (LinearMap.toSpanSingleton R _
        ((constantSheafAdj (Scheme.ProEt.topology D) (ModuleCat.{u + 1} S) hT).unit.app
            (ModuleCat.of S S) (1 : S))))

private theorem normalizedConstantMap_top {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (D : Scheme.{u}) (r : R) :
    (normalizedConstantMap φ D).hom.app (op (Scheme.ProEt.mk (𝟙 D)))
      ((toSheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
        (ModuleCat.of R R))).app (op (Scheme.ProEt.mk (𝟙 D))) r) =
      (toSheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
        (ModuleCat.of S S))).app (op (Scheme.ProEt.mk (𝟙 D))) (φ r) := by
  let hT : IsTerminal (Scheme.ProEt.mk (𝟙 D)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  let adj := constantSheafAdj (Scheme.ProEt.topology D) (ModuleCat.{u + 1} R) hT
  have h := (adj.homEquiv (ModuleCat.of R R)
    ((Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj
      (geoCartierConstant S D))).apply_symm_apply
    (ModuleCat.ofHom
      (Y := ((Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj
        (geoCartierConstant S D)).obj.obj
          (op (Scheme.ProEt.mk (𝟙 D))))
      (LinearMap.toSpanSingleton R _
        ((constantSheafAdj (Scheme.ProEt.topology D) (ModuleCat.{u + 1} S) hT).unit.app
            (ModuleCat.of S S) (1 : S))))
  have h' := congrArg (fun f ↦ f r) h
  change (normalizedConstantMap φ D).hom.app (op (Scheme.ProEt.mk (𝟙 D)))
    ((toSheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
      (ModuleCat.of R R))).app (op (Scheme.ProEt.mk (𝟙 D))) r) = _ at h'
  rw [h']
  change (φ r) • ((constantSheafAdj (Scheme.ProEt.topology D)
      (ModuleCat.{u + 1} S) (MorphismProperty.Over.mkIdTerminal _ _)).unit.app
      (ModuleCat.of S S) (1 : S)) = _
  rw [← map_smul]
  simp only [smul_eq_mul, mul_one]
  rfl

private theorem normalizedConstantMap_apply {R S : Type (u + 1)} [CommRing R]
    [CommRing S] (φ : R →+* S) (D : Scheme.{u}) (U : D.ProEtᵒᵖ) (r : R) :
    (normalizedConstantMap φ D).hom.app U
      ((toSheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
        (ModuleCat.of R R))).app U r) =
      (toSheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r) := by
  let hT : IsTerminal (Scheme.ProEt.mk (𝟙 D)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  let f := (hT.from U.unop).op
  let a := toSheafify (Scheme.ProEt.topology D)
    ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))
  let b := toSheafify (Scheme.ProEt.topology D)
    ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of S S))
  have hs := congrArg (fun q ↦ q r) (a.naturality f)
  have ht := congrArg (fun q ↦ q (φ r)) (b.naturality f)
  have hs2 : ((sheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
      (ModuleCat.of R R))).map f) (a.app (op (Scheme.ProEt.mk (𝟙 D))) r) = (a.app U) r := by
    simpa [a, ModuleCat.comp_apply] using hs.symm
  have ht2 : ((sheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
      (ModuleCat.of S S))).map f) (b.app (op (Scheme.ProEt.mk (𝟙 D))) (φ r)) =
      (b.app U) (φ r) := by
    simpa [b, ModuleCat.comp_apply] using ht.symm
  have hn := congrArg (fun q ↦ q (a.app (op (Scheme.ProEt.mk (𝟙 D))) r))
    ((normalizedConstantMap φ D).hom.naturality f)
  change (normalizedConstantMap φ D).hom.app U
      (((sheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
        (ModuleCat.of R R))).map f) (a.app
          (op (Scheme.ProEt.mk (𝟙 D))) r)) =
    ((sheafify (Scheme.ProEt.topology D) ((Functor.const D.ProEtᵒᵖ).obj
      (ModuleCat.of S S))).map f)
      ((normalizedConstantMap φ D).hom.app
        (op (Scheme.ProEt.mk (𝟙 D))) (a.app
          (op (Scheme.ProEt.mk (𝟙 D))) r)) at hn
  change (normalizedConstantMap φ D).hom.app U (a.app U r) = (b.app U) (φ r)
  rw [← hs2, ← ht2]
  rw [normalizedConstantMap_top] at hn
  exact hn

private noncomputable def proLineHomEquiv (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    (geoCartierLine A N hA T ⟶ P) ≃
      (T.rootsOfUnitySheaf N ⟶
        (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj
            ((comparisonLowerStar (ModuleCat.{u + 1} A) T).obj P)) :=
  ((comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ P).trans
    (lineHomEquiv T N A hA _)

private lemma proLineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (f : geoCartierLine A N hA T ⟶ P) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf N).obj.obj U) :
    (proLineHomEquiv T N A hA P f).hom.app U z =
      f.hom.app ((Scheme.toProEt T).op.obj U)
        (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          (finiteEtaleTateLine T N A hA)).hom.app U
            (finiteEtaleTateOneGenerator A N T hA U 1 z)) := by
  change (lineHomEquiv T N A hA _
    ((comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ P f)).hom.app U z = _
  rw [lineHomEquiv_generator]
  rfl

private noncomputable def lineCoefficientMap
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0) :
    geoCartierLine R N hR T ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj (geoCartierLine S N hS T) :=
  (proLineHomEquiv T N R hR _).symm
    (proLineHomEquiv T N S hS _ (𝟙 _))

private theorem lineCoefficientMap_one
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    (lineCoefficientMap φ T N hR hS).hom.app ((Scheme.toProEt T).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) T).unit.app
          (finiteEtaleTateLine T N R hR)).hom.app W
            (finiteEtaleTateOneGenerator R N T hR W 1 z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} S) T).unit.app
        (finiteEtaleTateLine T N S hS)).hom.app W
          (finiteEtaleTateOneGenerator S N T hS W 1 z) := by
  have h := Equiv.apply_symm_apply (proLineHomEquiv T N R hR
    ((Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj (geoCartierLine S N hS T)))
      (proLineHomEquiv T N S hS _ (𝟙 _))
  have hh := congrArg (fun f ↦ f.hom.app W z) h
  have ha := proLineHomEquiv_generator T N R hR _
    (lineCoefficientMap φ T N hR hS) W z
  have hb := proLineHomEquiv_generator T N S hS _ (𝟙 _) W z
  exact ha.symm.trans (hh.trans hb)

private theorem lineCoefficientMap_apply
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    (W : T.Etaleᵒᵖ) (a : R) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    (lineCoefficientMap φ T N hR hS).hom.app ((Scheme.toProEt T).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) T).unit.app
          (finiteEtaleTateLine T N R hR)).hom.app W
            (finiteEtaleTateOneGenerator R N T hR W a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} S) T).unit.app
        (finiteEtaleTateLine T N S hS)).hom.app W
          (finiteEtaleTateOneGenerator S N T hS W (φ a) z) := by
  rw [finiteEtaleGenerator_smul T N R hR W a z, map_smul, map_smul]
  rw [lineCoefficientMap_one]
  change (φ a) • ((comparisonAdjunction (ModuleCat.{u + 1} S) T).unit.app
    (finiteEtaleTateLine T N S hS)).hom.app W
      (finiteEtaleTateOneGenerator S N T hS W 1 z) = _
  rw [finiteEtaleGenerator_smul T N S hS W (φ a) z, map_smul]

private theorem lineCoefficientMap_universal
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    (H : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S)) :
    Function.Bijective (fun f : geoCartierLine S N hS T ⟶ H ↦
      lineCoefficientMap φ T N hR hS ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map f) := by
  let eR := proLineHomEquiv T N R hR
    ((Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj H)
  let eS := proLineHomEquiv T N S hS H
  have he (f : geoCartierLine S N hS T ⟶ H) :
      eR (lineCoefficientMap φ T N hR hS ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map f) = eS f := by
    ext W z
    have ha := proLineHomEquiv_generator T N R hR _
      (lineCoefficientMap φ T N hR hS ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map f) W z
    have hb := proLineHomEquiv_generator T N S hS H f W z
    exact ha.trans ((congrArg (fun x ↦ f.hom.app ((Scheme.toProEt T).op.obj W) x)
      (lineCoefficientMap_one φ T N hR hS W z)).trans hb.symm)
  constructor
  · intro f g h
    apply eS.injective
    exact (he f).symm.trans ((congrArg eR h).trans (he g))
  · intro f
    obtain ⟨g, hg⟩ := eS.surjective (eR f)
    exact ⟨g, eR.injective ((he g).trans hg)⟩

private theorem line_flat (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) : ObjectProperty.flat (geoCartierLine A N hA T) := by
  exact flat_comparisonUpperStar_obj
    (ObjectProperty.flat_of_tensorIso (finiteEtaleTateLineInverse T N hN A hA hT).rightIso)

private theorem constant_comparison_scalar {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) (D : Scheme.{u}) :
    (comparisonAdjunction (ModuleCat.{u + 1} R) D).unit.app
        (Etale.ordinaryFiniteConstant R D) ≫
      (comparisonLowerStar (ModuleCat.{u + 1} R) D).map
        (((comparisonUpperStarConstantSheafIso R D).app (ModuleCat.of R R)).hom ≫
          normalizedConstantMap φ D) =
    Etale.normalizedConstantMap φ D ≫
      (Sheaf.restrictScalars D.smallEtaleTopology φ).map
        ((comparisonAdjunction (ModuleCat.{u + 1} S) D).unit.app
          (Etale.ordinaryFiniteConstant S D) ≫
          (comparisonLowerStar (ModuleCat.{u + 1} S) D).map
            ((comparisonUpperStarConstantSheafIso S D).app (ModuleCat.of S S)).hom) := by
  let adj := constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} R)
    (Scheme.Etale.isTerminalMkId D)
  apply (adj.homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (normalizedConstantMap φ D).hom.app (op (Scheme.ProEt.mk (𝟙 D)))
    ((((comparisonUpperStarConstantSheafIso R D).app (ModuleCat.of R R)).hom).hom.app
      (op (Scheme.ProEt.mk (𝟙 D)))
      (((comparisonAdjunction (ModuleCat.{u + 1} R) D).unit.app
        (Etale.ordinaryFiniteConstant R D)).hom.app (op (Scheme.Etale.mk (𝟙 D)))
        ((toSheafify D.smallEtaleTopology
          ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of R R))).app
            (op (Scheme.Etale.mk (𝟙 D))) a))) = _
  rw [comparison_constant_generator, normalizedConstantMap_apply]
  change _ = (((comparisonUpperStarConstantSheafIso S D).app
    (ModuleCat.of S S)).hom).hom.app (op (Scheme.ProEt.mk (𝟙 D)))
      (((comparisonAdjunction (ModuleCat.{u + 1} S) D).unit.app
        (Etale.ordinaryFiniteConstant S D)).hom.app (op (Scheme.Etale.mk (𝟙 D)))
        ((Etale.normalizedConstantMap φ D).hom.app (op (Scheme.Etale.mk (𝟙 D)))
          ((toSheafify D.smallEtaleTopology
            ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of R R))).app
              (op (Scheme.Etale.mk (𝟙 D))) a)))
  rw [Etale.normalizedConstantMap_apply, comparison_constant_generator]

private theorem source_comparison_unit (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ≫
      (comparisonLowerStar (ModuleCat.{u + 1} A) Z).map
        (geoCartierSourceComparison A i) =
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonAdjunction (ModuleCat.{u + 1} A) D).unit.app
          (Etale.ordinaryFiniteConstant A D) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) D).map
          ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom) ≫
      (lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.app
        (geoCartierConstant A D) := by
  have hm := unit_mateEquiv_symm
    (comparisonAdjunction (ModuleCat.{u + 1} A) D)
    (comparisonAdjunction (ModuleCat.{u + 1} A) Z)
    (lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv
    (Etale.ordinaryFiniteConstant A D)
  change _ = (comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ≫
    (comparisonLowerStar (ModuleCat.{u + 1} A) Z).map
      ((lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app
        (Etale.ordinaryFiniteConstant A D)) at hm
  unfold geoCartierSourceComparison
  rw [Functor.map_comp, ← Category.assoc]
  change _ ≫ (comparisonLowerStar (ModuleCat.{u + 1} A) Z).map _ = _
  rw [← hm]
  simp only [Functor.map_comp, Category.assoc]
  have hh := (lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.naturality
    ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom
  simp only [Functor.comp_map] at hh
  erw [← hh]
  rfl

private theorem source_comparison_scalar {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
        ((Etale.lowerStar (ModuleCat.{u + 1} R) i).obj (Etale.ordinaryFiniteConstant R D)) ≫
      (comparisonLowerStar (ModuleCat.{u + 1} R) Z).map
        (geoCartierSourceComparison R i ≫
          (lowerStar (ModuleCat.{u + 1} R) i).map (normalizedConstantMap φ D)) =
    (Etale.lowerStar (ModuleCat.{u + 1} R) i).map (Etale.normalizedConstantMap φ D) ≫
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).map
        ((comparisonAdjunction (ModuleCat.{u + 1} S) Z).unit.app
          ((Etale.lowerStar (ModuleCat.{u + 1} S) i).obj (Etale.ordinaryFiniteConstant S D)) ≫
          (comparisonLowerStar (ModuleCat.{u + 1} S) Z).map (geoCartierSourceComparison S i)) := by
  rw [Functor.map_comp, ← Category.assoc, source_comparison_unit,
    source_comparison_unit]
  have hc := constant_comparison_scalar φ D
  ext W x
  have hcx := ConcreteCategory.congr_hom (congrArg
    (fun f ↦ f.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W)) hc) x
  have ha (B : Type (u + 1)) [CommRing B] :
      ((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} B)).inv.app
        (geoCartierConstant B D)).hom.app W = 𝟙 _ := by
    dsimp [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso]
    change (𝟙 _) ≫ (geoCartierConstant B D).obj.map (𝟙 _) ≫ (𝟙 _) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  let V := (MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W
  change (normalizedConstantMap φ D).hom.app
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
        ((Scheme.toProEt Z).obj W.unop)))
      (((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} R)).inv.app
          (geoCartierConstant R D)).hom.app W
        (((comparisonLowerStar (ModuleCat.{u + 1} R) D).map
            ((comparisonUpperStarConstantSheafIso R D).app (ModuleCat.of R R)).hom).hom.app V
          (((comparisonAdjunction (ModuleCat.{u + 1} R) D).unit.app
              (Etale.ordinaryFiniteConstant R D)).hom.app V x))) =
    ((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} S)).inv.app
        (geoCartierConstant S D)).hom.app W
      (((comparisonLowerStar (ModuleCat.{u + 1} S) D).map
          ((comparisonUpperStarConstantSheafIso S D).app (ModuleCat.of S S)).hom).hom.app V
        (((comparisonAdjunction (ModuleCat.{u + 1} S) D).unit.app
            (Etale.ordinaryFiniteConstant S D)).hom.app V
          ((Etale.normalizedConstantMap φ D).hom.app V x)))
  rw [ha R, ha S]
  exact hcx

private theorem supported_flat (R : Type (u + 1)) [CommRing R] [Finite R]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    ObjectProperty.flat
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R D)) := by
  exact ObjectProperty.prop_of_iso ObjectProperty.flat (asIso (geoCartierSourceComparison R i))
    (flat_comparisonUpperStar_obj (Etale.finite_constant_flat Z R i))

private theorem supported_universal {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (H : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S)) :
    Function.Bijective (fun f :
      (lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D) ⟶ H ↦
      (lowerStar (ModuleCat.{u + 1} R) i).map (normalizedConstantMap φ D) ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).map f) := by
  let eR := ((asIso (geoCartierSourceComparison R i)).symm.homCongr (Iso.refl _)).trans
    ((comparisonAdjunction (ModuleCat.{u + 1} R) Z).homEquiv _
      ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj H))
  let eS := ((asIso (geoCartierSourceComparison S i)).symm.homCongr (Iso.refl _)).trans
    ((comparisonAdjunction (ModuleCat.{u + 1} S) Z).homEquiv _ H)
  have hη := Etale.constant_ordinary_scalar_unit D φ (Etale.normalizedConstantMap φ D)
    (Etale.normalizedConstantMap_apply φ D)
  have hb := Etale.finite_ordinary_scalar_unit Z φ i _ _ _ hη
    ((comparisonLowerStar (ModuleCat.{u + 1} S) Z).obj H)
  have he (f : (lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D) ⟶ H) :
      eR ((lowerStar (ModuleCat.{u + 1} R) i).map (normalizedConstantMap φ D) ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).map f) =
      (Etale.lowerStar (ModuleCat.{u + 1} R) i).map (Etale.normalizedConstantMap φ D) ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).map (eS f) := by
    change (comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app _ ≫
      (comparisonLowerStar (ModuleCat.{u + 1} R) Z).map
        (geoCartierSourceComparison R i ≫
          (lowerStar (ModuleCat.{u + 1} R) i).map (normalizedConstantMap φ D) ≫
            (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).map f) = _
    rw [← Category.assoc (geoCartierSourceComparison R i), Functor.map_comp,
      ← Category.assoc, source_comparison_scalar]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hfun : (fun f :
      (lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D) ⟶ H ↦ eR
      ((lowerStar (ModuleCat.{u + 1} R) i).map (normalizedConstantMap φ D) ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).map f)) =
      (fun f ↦ (Etale.lowerStar (ModuleCat.{u + 1} R) i).map
        (Etale.normalizedConstantMap φ D) ≫
          (Sheaf.restrictScalars Z.smallEtaleTopology φ).map (eS f)) := funext he
  have hb' : Function.Bijective (fun f :
      (lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D) ⟶ H ↦
      (Etale.lowerStar (ModuleCat.{u + 1} R) i).map (Etale.normalizedConstantMap φ D) ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).map (eS f)) := by
    have hh := hb.comp eS.bijective
    change Function.Bijective (fun f ↦
      ((Etale.lowerStar (ModuleCat.{u + 1} R) i).map (Etale.normalizedConstantMap φ D) ≫
        𝟙 _) ≫ (Sheaf.restrictScalars Z.smallEtaleTopology φ).map (eS f)) at hh
    simpa only [Category.comp_id] using hh
  have hb'' := hfun.symm ▸ hb'
  exact (Function.Bijective.of_comp_iff' eR.bijective _).mp hb''

/-- The supported constant and the comparison Tate line admit their normalized
unbounded derived coefficient units. No divisor ideal or cycle class is involved.
Source: blueprint sk-lem-geo-cartier.proof.md, finite coefficient extension paragraph
and opening comparison paragraph (blueprint: lem-sfb-cartier-normalized-scalar-units).
Proof: On the ordinary etale site, form the constant coefficient map by sheafifying
r mapped to phi(r). Form the roots coefficient map by sheafifying the balanced map
r tensor z mapped to phi(r) tensor z. The supported constant has stalk R on the
closed support and zero elsewhere, and the roots line is locally free of rank one
because N is positive and invertible. Both are flat over the constant R sheaf.
The ordinary tensor comparisons identify their scalar extensions with the supported
S constant and the S roots line. The flat-source derived scalar adjunction therefore
gives their Hom universal properties against every unbounded complex, even if S is
not flat over R. Exact comparison inverse image commutes with derived scalar
extension. Transport the two units through this comparison, using the closed-source
mate for the first and the defining comparison pullback of the roots line for the
second. The comparison adjunction unit commutes with coefficient maps, giving the
stated formula on pure roots. The constant comparison sends each constant generator
to itself, giving the first formula. Closed direct image of this constant map is
exactly the supported unit, by the mate unit equation. These arguments also cover
empty support, the zero ring, and the identity coefficient map. -/
theorem geoCartier_normalized_scalar_units
    (R S : Type (u + 1)) [CommRing R] [CommRing S] [Finite R] [Finite S]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (hS : (N : S) = 0)
    (φ : R →+* S) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hZ : IsUnit (N : Γ(Z, ⊤))) :
  ∃ (η : geoCartierConstant R D ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant S D))
    (θ : geoCartierLine R N hR Z ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj (geoCartierLine S N hS Z)),
    (∀ (W : D.ProEtᵒᵖ) (a : R),
      η.hom.app W ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))).app W a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of S S))).app W (φ a)) ∧
    (∀ (W : Z.Etaleᵒᵖ) (a : R) (z : (Z.rootsOfUnitySheaf N).obj.obj W),
      θ.hom.app ((Scheme.toProEt Z).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
          (Scheme.finiteEtaleTateLine Z N R hR)).hom.app W
            (Scheme.finiteEtaleTateOneGenerator R N Z hR W a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} S) Z).unit.app
        (Scheme.finiteEtaleTateLine Z N S hS)).hom.app W
          (Scheme.finiteEtaleTateOneGenerator S N Z hS W (φ a) z)) ∧
    GeoCartierScalarUnit φ Z
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    GeoCartierScalarUnit φ Z (geoCartierLine R N hR Z) (geoCartierLine S N hS Z) θ := by
  refine ⟨normalizedConstantMap φ D, lineCoefficientMap φ Z N hR hS,
    normalizedConstantMap_apply φ D, lineCoefficientMap_apply φ Z N hR hS, ?_, ?_⟩
  · exact geoCartierScalarUnit_of_scalarUniversal φ Z _ _ _
      (SheafExactDegreeZero.scalarUniversal_of_flat _ φ _ _ _
        (supported_flat R i) (supported_universal φ i))
  · exact geoCartierScalarUnit_of_scalarUniversal φ Z _ _ _
      (SheafExactDegreeZero.scalarUniversal_of_flat _ φ _ _ _
        (line_flat R Z N hN hR hZ) (lineCoefficientMap_universal φ Z N hR hS))

end AlgebraicGeometry.ProEtale
