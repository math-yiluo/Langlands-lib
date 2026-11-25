/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.CategoryTheory.Conj
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
import Mathlib.CategoryTheory.Conj
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Quotient

/-! # Integral fibre paths from finite level evaluation

## References

* Weil II (1.1.1) b), p.146
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber
  GrothendieckTopology.Point.presheafFiber

end AlgebraicGeometry.Scheme
