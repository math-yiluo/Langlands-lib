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
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalIntegralGaloisFunctor

/-! # Integral reconstruction from finite Galois modules

## References

* Weil II (1.1.1), (1.1.6)
* Stanford Weil II seminar L19, Proposition 1.1.9
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

end AlgebraicGeometry.Scheme
