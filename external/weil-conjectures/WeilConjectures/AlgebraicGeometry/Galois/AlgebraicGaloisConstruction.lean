/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalGaloisConstruction

/-! # Algebraic reconstruction from rational Galois modules

Source: Weil II (1.1.1), (1.1.6); Stanford Weil II seminar L19, Proposition 1.1.9.
(blueprint: new-e7-algebraic-galois-construction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

end AlgebraicGeometry.Scheme
