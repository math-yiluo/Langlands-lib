/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.PBCFiltration
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
public import WeilConjectures.CategoryTheory.FilteredComplexSpectralSequence
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.Algebra.Homology.TensorHomologyPairing

/-! # Bounded Künneth spectral sequence

Source: Stacks Project, `more-algebra.tex`, Tag 0H7Z, lemma-kunneth-spectral-sequence;
the p=0 product calculation is the Products and Tor equation `simple-tor-product`
(blueprint: lem-pur-kunneth-flat-spectral-sequence).

This file provides the terms of the bounded Künneth spectral sequence: the cohomology
modules, the Tor modules of the `E₂` page, the direct-sum `E₂` term `kunnethE₂Term`, the
abutment `derivedTensorHomology`, and the comparison maps for complex representatives.
The spectral sequence itself, with its finite abutment filtration and the product
description of the `p = 0` edge, is not yet formalized here.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

/-- The cohomology module of a derived object.
Source: Stacks Project, Tag 0H7Z (blueprint: lem-pur-kunneth-flat-spectral-sequence). -/
abbrev derivedModuleHomology (R : Type u) [CommRing R]
    [IsGrothendieckAbelian.{u} (ModuleCat.{u} R)]
    [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) : ModuleCat.{u} R :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K

/-- The Tor module used on the E₂ page, with negative degrees interpreted as zero.
Source: Stacks Project, Tag 0H7Z (blueprint: lem-pur-kunneth-flat-spectral-sequence). -/
noncomputable def derivedModuleTor (R : Type u) [CommRing R]
    [IsGrothendieckAbelian.{u} (ModuleCat.{u} R)]
    [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (A B : ModuleCat.{u} R) (n : ℤ) : ModuleCat.{u} R :=
  if _hn : 0 ≤ n then
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-n)).obj
      (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj A)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj B))
  else
    ModuleCat.of R (⊥ : Submodule R R)

/-- The concrete lax-monoidal comparison on two complex representatives.
Source: Stacks Project, Tags 064L and 06Y0 (blueprint:
lem-pur-kunneth-flat-spectral-sequence). -/
noncomputable abbrev laxDerivedTensorMap (R : Type u) [CommRing R]
    [IsGrothendieckAbelian.{u} (ModuleCat.{u} R)]
    [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q ⟶
      DerivedCategory.Q.obj (P ⊗ Q) :=
  letI : (DerivedCategory.Q (C := ModuleCat.{u} R)).LaxMonoidal :=
    inferInstance
  Functor.LaxMonoidal.μ (DerivedCategory.Q (C := ModuleCat.{u} R)) P Q

/-- The direct-sum E₂ term indexed by pairs of cohomological degrees.
Source: Stacks Project, `more-algebra.tex`, Tag 0H7Z (blueprint:
lem-pur-kunneth-flat-spectral-sequence). -/
abbrev kunnethE₂Term (R : Type u) [CommRing R]
    [IsGrothendieckAbelian.{u} (ModuleCat.{u} R)]
    [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : DerivedCategory (ModuleCat.{u} R)) (p q : ℤ) : ModuleCat.{u} R :=
  ModuleCat.of R (DirectSum
    {ij : ℤ × ℤ // ij.1 + ij.2 = q}
    (fun ij ↦ (derivedModuleTor R (derivedModuleHomology R K ij.1.1)
      (derivedModuleHomology R L ij.1.2) (-p) : Type u)))

/-- The abutment cohomology object used by the edge map.
Source: Stacks Project, Tag 0H7Z (blueprint: lem-pur-kunneth-flat-spectral-sequence). -/
abbrev derivedTensorHomology (R : Type u) [CommRing R]
    [IsGrothendieckAbelian.{u} (ModuleCat.{u} R)]
    [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) : ModuleCat.{u} R :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
    ((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K |>.obj L)

/-- The homology identifications induced by the specified representative roofs.
Source: Stacks Project, Tags 064L and 06Y0 (blueprint: lem-pur-kunneth-flat-spectral-sequence). -/
noncomputable def representativeHomologyIso (R : Type u) [CommRing R]
    [IsGrothendieckAbelian.{u} (ModuleCat.{u} R)]
    [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (K : DerivedCategory (ModuleCat.{u} R))
    (eP : DerivedCategory.Q.obj P ≅ K) (i : ℤ) :
    derivedModuleHomology R K i ≅ ModuleCat.of R (P.homology i : Type u) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso eP.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P

end CategoryTheory
