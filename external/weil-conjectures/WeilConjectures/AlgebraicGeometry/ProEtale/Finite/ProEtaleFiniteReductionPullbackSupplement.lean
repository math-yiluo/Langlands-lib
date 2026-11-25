/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Topology.Category.Profinite.Limits
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteReductionPullback

/-!
# Base change for one normalized finite reduction

The finite constant-sheaf identifications and the adjunction-mate calculation for a
single continuous finite quotient. This calculation is independent of the integral
limit and of its ring-compatible comparison.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarLowerStarAdjunction constantSheafΓAdj
  globalSectionsLowerStarIso

private abbrev finitePoint : FintypeCat.{u} := FintypeCat.of PUnit.{u + 1}

private noncomputable def finitePointTerminal (X : Scheme.{u}) :
    IsTerminal ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj finitePoint)) := by
  have : PreservesFiniteLimits (profiniteToProEtOf X) := by
    have : PreservesFiniteLimits profiniteToProEt.{u} := inferInstance
    have : PreservesFiniteLimits
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) := inferInstance
    exact comp_preservesFiniteLimits _ _
  exact Profinite.isTerminalPUnit.isTerminalObj (profiniteToProEtOf X) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] pointUpperStarLowerStarAdjunction

set_option backward.isDefEq.respectTransparency false in
private theorem constantCommute_unit {C D B : Type*} [Category* C] [Category* D]
    [Category* B] (J : GrothendieckTopology C) (U : D ⥤ B)
    [HasWeakSheafify J D] [HasWeakSheafify J B]
    [J.HasSheafCompose U] [J.PreservesSheafification U] (A : D) :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) U ≫
        ((constantCommuteCompose J U).hom.app A).hom =
      (Functor.constComp Cᵒᵖ A U).hom ≫
        toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac, ← toSheafify_naturality]

private noncomputable abbrev finiteAbSheaf (X : Scheme.{u}) (R : Type u) [CommRing R] :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} R))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantRingAb_unit (X : Scheme.{u}) (A : CommRingCat.{u + 1})
    (V : X.ProEtᵒᵖ) (x : A) :
    (sfbConstantRingAbIso X A).hom.hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj A)).app V x) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V x := by
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have h₁ := congrArg (fun t ↦ t.app V x)
    (constantCommute_unit (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) A)
  have h₂ := congrArg (fun t ↦ t.app V x)
    (constantCommute_unit (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A))
  exact (congrArg (fun z ↦ ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).hom.app
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A)).hom.app V z) h₁).trans h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def finiteRepresentation (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] :
    (finiteAbSheaf X R).obj ⋙ forget Ab.{u + 1} ≅
      uliftYoneda.{u + 1}.obj
        ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj (FintypeCat.of R))) :=
  (sheafToPresheaf _ _).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} R))) ≪≫ a.app (FintypeCat.of R)

end AlgebraicGeometry.ProEtale
