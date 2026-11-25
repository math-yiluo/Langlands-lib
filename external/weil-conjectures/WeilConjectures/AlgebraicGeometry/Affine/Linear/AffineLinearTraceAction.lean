/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
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
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Linear changes of coordinates preserve the affine-space counit trace

Source: blueprint sec-smooth-purity/sk-prop-an/lem-amb-linear-trace-invariance.md,
Proof paragraphs 1 and 2 (blueprint: def-amb-affine-linear-trace-action).

The coefficient complex is the existing coordinate-tower model of A(d)[2d]. Its
canonical inverse-image comparison is constructed by descent from the ordered tensor
of d shifted Tate lines on the base. The action uses compact-support exchange for the
actual Cartesian square (a_g, 1_S), followed by this coefficient comparison. It is then
transported along the existing bounded-below compact-support comparison to the tower.

## Main definitions and statement

- `affineTraceLinearMap`: the concrete polynomial map v ↦ gv in the tower model.
- `affineLinearCoefficientPullback`: the canonical comparison on A(d)[2d].
- `affineLinearTraceAction`: exchange followed by the coefficient comparison.
- `affineSpaceLinearTraceInvariance`: the specified action preserves the specified counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- The linear coordinate map in the existing tower model: pull the matrix entries
back from S, take the usual finite sums, and use the canonical affine-space coordinate
isomorphism. Source: blueprint linear-trace lemma, statement and proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineTraceLinearMap (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    affineTraceTower S d ⟶ affineTraceTower S d :=
  AffineSpace.homOfVector (affineTraceProjection S d)
    (fun i : ULift.{u} (Fin d) ↦ ∑ j : Fin d,
      (affineTraceProjection S d).appTop.hom (g i.down j) * affineTraceCoordinate S d j) ≫
    (affineTraceAffineSpaceIso S d).inv

private lemma linear_iso_over (S : Scheme.{u}) (d : ℕ) :
    (affineTraceAffineSpaceIso S d).inv ≫ affineTraceProjection S d =
      AffineSpace (ULift.{u} (Fin d)) S ↘ S := by
  apply (cancel_epi (affineTraceAffineSpaceIso S d).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (AffineSpace.homOfVector_over _ _).symm

private lemma linear_iso_coord (S : Scheme.{u}) (d : ℕ) (j : Fin d) :
    (affineTraceAffineSpaceIso S d).inv.appTop (affineTraceCoordinate S d j) =
      AffineSpace.coord S (ULift.up j) := by
  have h := congrArg (fun f ↦ f.appTop (AffineSpace.coord S (ULift.up j)))
    (affineTraceAffineSpaceIso S d).inv_hom_id
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
    AffineSpace.homOfVector_appTop_coord, Scheme.Hom.id_appTop, ConcreteCategory.id_apply] using h

private lemma linear_over (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    affineTraceLinearMap S d g ≫ affineTraceProjection S d = affineTraceProjection S d := by
  simp only [affineTraceLinearMap, Category.assoc, linear_iso_over,
    AffineSpace.homOfVector_over]

private lemma linear_coord (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) (j : Fin d) :
    (affineTraceLinearMap S d g).appTop (affineTraceCoordinate S d j) =
      ∑ i : Fin d, (affineTraceProjection S d).appTop (g j i) *
        affineTraceCoordinate S d i := by
  simp only [affineTraceLinearMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    linear_iso_coord, AffineSpace.homOfVector_appTop_coord]

private lemma linear_ext (S : Scheme.{u}) (d : ℕ)
    {X : Scheme.{u}} {f g : X ⟶ affineTraceTower S d}
    (hp : f ≫ affineTraceProjection S d = g ≫ affineTraceProjection S d)
    (hc : ∀ j, f.appTop (affineTraceCoordinate S d j) =
      g.appTop (affineTraceCoordinate S d j)) : f = g := by
  apply (cancel_mono (affineTraceAffineSpaceIso S d).hom).mp
  apply AffineSpace.hom_ext
  · simpa only [Category.assoc, affineTraceAffineSpaceIso, asIso_hom,
      affineTraceToAffineSpace, AffineSpace.homOfVector_over] using hp
  · rintro ⟨j⟩
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
      AffineSpace.homOfVector_appTop_coord] using hc j

private lemma linear_one (S : Scheme.{u}) (d : ℕ) :
    affineTraceLinearMap S d 1 = 𝟙 _ := by
  apply linear_ext S d
  · simpa only [Category.id_comp] using linear_over S d 1
  · intro j
    simp [linear_coord, Matrix.one_apply]

private lemma linear_comp (S : Scheme.{u}) (d : ℕ)
    (g h : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    affineTraceLinearMap S d g ≫ affineTraceLinearMap S d h =
      affineTraceLinearMap S d (h * g) := by
  apply linear_ext S d
  · simp only [Category.assoc, linear_over]
  · intro j
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linear_coord,
      map_sum, map_mul]
    have hp (r : Γ(S, ⊤)) :
        (affineTraceLinearMap S d g).appTop ((affineTraceProjection S d).appTop r) =
          (affineTraceProjection S d).appTop r := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, linear_over]
    simp only [hp, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

/-- The concrete linear coordinate map is an automorphism, and its square over the
identity is Cartesian. Source: linear-trace invariance, proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
theorem affineTraceLinearMap_isPullback (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    IsPullback (affineTraceLinearMap S d g) (affineTraceProjection S d)
      (affineTraceProjection S d) (𝟙 S) := by
  have : IsIso (affineTraceLinearMap S d g) :=
    ⟨⟨affineTraceLinearMap S d g⁻¹, by rw [linear_comp, inv_mul_cancel, linear_one],
      by rw [linear_comp, mul_inv_cancel, linear_one]⟩⟩
  exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using linear_over S d g⟩

/-- The concrete linear map is over its base.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
theorem affineTraceLinearMap_over (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    affineTraceLinearMap S d g ≫ affineTraceProjection S d = affineTraceProjection S d :=
  linear_over S d g

/-- Pulling back a tower coordinate gives the corresponding matrix-vector product.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
theorem affineTraceLinearMap_coordinate (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) (j : Fin d) :
    (affineTraceLinearMap S d g).appTop (affineTraceCoordinate S d j) =
      ∑ i : Fin d, (affineTraceProjection S d).appTop (g j i) *
        affineTraceCoordinate S d i :=
  linear_coord S d g j

/-- The identity matrix gives the identity of the actual tower.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
theorem affineTraceLinearMap_one (S : Scheme.{u}) (d : ℕ) :
    affineTraceLinearMap S d 1 = 𝟙 _ :=
  linear_one S d

/-- The ordered coordinate tower commutes with base change.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
theorem affineTraceMap_isPullback {S' S : Scheme.{u}} (f : S' ⟶ S) (d : ℕ) :
    IsPullback (affineTraceMap f d) (affineTraceProjection S' d)
      (affineTraceProjection S d) f := by
  induction d with
  | zero => exact IsPullback.id_vert f
  | succ d ih =>
    exact (AffineSpace.isPullback_map (n := PUnit.{u + 1})
      (affineTraceMap f d)).paste_vert ih

set_option backward.isDefEq.respectTransparency.types false in
private lemma traceMap_coordinate {S' S : Scheme.{u}} (f : S' ⟶ S) (d : ℕ)
    (j : Fin d) :
    (affineTraceMap f d).appTop (affineTraceCoordinate S d j) =
      affineTraceCoordinate S' d j := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [affineTraceCoordinate, Fin.lastCases_last, affineTraceMap] using!
        (AffineSpace.map_appTop_coord (affineTraceMap f d) PUnit.unit)
    · simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      change (affineTraceMap f (d + 1)).appTop
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘
          affineTraceTower S d).appTop (affineTraceCoordinate S d i)) = _
      erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      change ((AffineSpace.map PUnit.{u + 1} (affineTraceMap f d)) ≫
        AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d).appTop _ = _
      rw [AffineSpace.map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih]

/-- Linear coordinate maps commute with base change of their matrix entries.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
theorem affineTraceLinearMap_baseChange {S' S : Scheme.{u}} (f : S' ⟶ S) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    affineTraceLinearMap S' d (Matrix.GeneralLinearGroup.map f.appTop.hom g) ≫
        affineTraceMap f d =
      affineTraceMap f d ≫ affineTraceLinearMap S d g := by
  apply linear_ext S d
  · rw [Category.assoc, (affineTraceMap_isPullback f d).w,
      ← Category.assoc, linear_over, Category.assoc, linear_over]
    exact (affineTraceMap_isPullback f d).w.symm
  · intro j
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, traceMap_coordinate,
      linear_coord, map_sum, map_mul]
    congr 1
    funext i
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      (affineTraceMap_isPullback f d).w, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    rfl

namespace Etale

/-- The identity inverse-image comparison, using the existing exact-derived comparison.
Source: blueprint linear-trace lemma, identity normalization in proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineLinearPullbackId (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ordinaryFinitePullback A (𝟙 S) ≅ 𝟭 (DerivedCategoryModule A S) :=
  leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S) ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) S) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The ordered tensor product of d shifted finite Tate lines on the base, representing
A_S(d)[2d]. The zero stage is the constant coefficient complex. No orientation is chosen.
Source: blueprint linear-trace lemma, K_T in proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineLinearBaseCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) : ℕ → DerivedCategoryModule A S
  | 0 => ordinaryFiniteUnit A S
  | d + 1 => (derivedTensorRight (ModuleCat.{u + 1} A) S
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj
        (affineLinearBaseCoefficient A N hA S d)

/-- One coordinate right functor, canonically expressed as inverse image of a tensor
with the shifted line on its base. This uses tensor inverse image, composition, and
normalized finite Tate inverse image, in that order.
Source: blueprint linear-trace lemma, coefficient identification in proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineLinearLineDescent (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (K : DerivedCategoryModule A S) :
    (affineTraceLineRight A N hA S).obj K ≅
      (ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} S ↘ S)).obj
        ((derivedTensorRight (ModuleCat.{u + 1} A) S
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj K) :=
  ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart S)
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≪≫
    ordinaryFiniteTensorRightMapIso A (AffineSpace PUnit.{u + 1} S)
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart S)
        (ProjectiveLine S ↘ S) (AffineSpace PUnit.{u + 1} S ↘ S)
        (ProjectiveLine.affineChart_over S).symm).symm.app K)
      (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine.affineChart S)
        (affineTraceProjectiveInvertible N S hS) ≪≫
        (ordinaryFiniteShiftedLinePullback A N hA t
          (AffineSpace PUnit.{u + 1} S ↘ S) hS).symm) ≪≫
    (ordinaryFiniteTensorPullback A (AffineSpace PUnit.{u + 1} S ↘ S) K
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).symm

/-- One induction step in the canonical coefficient descent, with the preceding
comparison explicit. Source: blueprint linear-trace lemma, proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineLinearCoefficientDescentStep (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (e : (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (affineLinearBaseCoefficient A N hA S d)) :
    (affineTraceLineRight A N hA (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (ordinaryFinitePullback A
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) ≫
          affineTraceProjection S d)).obj
        ((derivedTensorRight (ModuleCat.{u + 1} A) S
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj
            (affineLinearBaseCoefficient A N hA S d)) :=
  affineLinearLineDescent A N hA t (affineTraceTower S d)
    (affineTraceInvertible N S hS d)
    ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≪≫
  (ordinaryFinitePullback A
    (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).mapIso
    (ordinaryFiniteTensorRightMapIso A (affineTraceTower S d) e
      (ordinaryFiniteShiftedLinePullback A N hA t (affineTraceProjection S d) hS).symm ≪≫
    (ordinaryFiniteTensorPullback A (affineTraceProjection S d)
      (affineLinearBaseCoefficient A N hA S d)
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).symm) ≪≫
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
    (affineTraceProjection S d)).symm.app (affineLinearBaseCoefficient A N hA S (d + 1))

/-- Descend the existing tower coefficient to the ordered shifted Tate tensor on S.
Every component is a canonical tensor, inverse-image, or normalized Tate comparison.
Source: blueprint linear-trace lemma, coefficient identification in proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineLinearCoefficientDescent (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (affineLinearBaseCoefficient A N hA S d) :=
  Nat.rec (motive := fun e ↦
    (affineTraceRight A N hA S e).obj (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePullback A (affineTraceProjection S e)).obj
        (affineLinearBaseCoefficient A N hA S e))
    ((affineLinearPullbackId A S).app (ordinaryFiniteUnit A S)).symm
    (fun e r ↦ affineLinearCoefficientDescentStep A N hA t S hS e r) d

/-- The canonical Tate comparison for an S-endomorphism of affine space, obtained by
pulling the descended base coefficient through a ≫ p = p. In particular this is the
usual roots-of-unity/tensor/shift comparison, with no scalar automorphism inserted.
Source: blueprint linear-trace lemma, theta_a in proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineLinearCoefficientPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (ha : a ≫ affineTraceProjection S d = affineTraceProjection S d) :
    (ordinaryFinitePullback A a).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) :=
  (ordinaryFinitePullback A a).mapIso (affineLinearCoefficientDescent A N hA t S hS d) ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a (affineTraceProjection S d)
      (affineTraceProjection S d) ha.symm).symm.app
        (affineLinearBaseCoefficient A N hA S d) ≪≫
    (affineLinearCoefficientDescent A N hA t S hS d).symm

/-- The specified bounded-below tower comparison, read in the ordinary unbounded
category using the two existing restriction-compatibility isomorphisms.
Source: blueprint linear-trace lemma, identification with F_S in proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineLinearCompactComparison (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceLeft A S d).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) :=
  let K : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 S hS d).2.1))⟩
  ((affineTracePlusCompatibility A S d).app K).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      ((affineTraceCompactSupportComparison A S d).app K) ≪≫
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).app K

/-- The pullback action: identify the tower with Rp_d!, insert inverse image along the
identity on S, apply exchange for the actual square, apply the canonical Tate comparison,
and return through the same tower comparison.
Source: blueprint linear-trace lemma, definition of rho_g in proof paragraph 1
(blueprint: def-amb-affine-linear-trace-action). -/
def affineLinearTraceAction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (sq : IsPullback a (affineTraceProjection S d) (affineTraceProjection S d) (𝟙 S)) :
    (affineTraceLeft A S d).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      (affineTraceLeft A S d).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) :=
  (affineLinearCompactComparison N hN A hA S hS d).hom ≫
    (affineLinearPullbackId A S).inv.app
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ≫
    (rightDerivedLowerShriekBaseChangeMap A sq).app _ ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
      (affineLinearCoefficientPullback A N hA t S hS d a
        (sq.w.trans (Category.comp_id _))).hom ≫
    (affineLinearCompactComparison N hN A hA S hS d).inv

end Etale
end AlgebraicGeometry
