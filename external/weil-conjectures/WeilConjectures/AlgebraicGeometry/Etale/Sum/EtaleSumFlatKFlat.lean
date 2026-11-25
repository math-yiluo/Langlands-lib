/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.Additive

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-!
# Étale sum extension preserves flatness and K-flatness

Source: Stacks Project, More on Étale Cohomology, Tag 0GKF
(`lemma-f-shriek-projection`), with the unbounded total-tensor expansion recorded in
(blueprint: lem-pur-etale-sum-flat-kflat).

The three helper functors apply the published constant-scalar equivalence, its
canonical coefficient-ring transport, and the published sum extension degreewise.
They introduce no choice of a module action, extension functor, or tensor product.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Realize module-valued étale sheaves as modules over the constant commutative
ring sheaf, using the existing constant-scalar extension and canonical ring isomorphism.
Source: Stacks, Modules on Sites, Tags 093I and 03CV; the coefficient convention in
Tag 0GKF (blueprint: lem-pur-etale-sum-flat-kflat). -/
def etaleSumFlatModuleRealization (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      SheafOfModules.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))) :=
  etaleConstantModuleFunctor T A ⋙
    SheafOfModules.pushforward (F := 𝟭 T.Etale)
      (constantModuleHomRingIso T.smallEtaleTopology A).inv

/-- Apply the canonical constant-coefficient realization degreewise, including to
unbounded complexes. Source: Stacks Tag 0GKF and the total-tensor expansion in
(blueprint: lem-pur-etale-sum-flat-kflat). -/
def etaleSumFlatComplexRealization (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of A)))) ℤ :=
  letI := etaleConstantModuleFunctor_isEquivalence T A
  (etaleConstantModuleFunctor T A ⋙
    SheafOfModules.pushforward (F := 𝟭 T.Etale)
      (constantModuleHomRingIso T.smallEtaleTopology A).inv).mapHomologicalComplex
        (ComplexShape.up ℤ)

end AlgebraicGeometry.Scheme
