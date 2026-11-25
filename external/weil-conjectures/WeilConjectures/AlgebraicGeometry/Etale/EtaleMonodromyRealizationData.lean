/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSized
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement

/-!
# Integral normalization data for rational monodromy realization

Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
and the proof of Corollary 6.8.5
(blueprint: def-sfb-monodromy-realization-data).

The integral model is specified by a limit cone over finite etale local systems,
with the quotient maps and monodromy prescribed on the geometric fibre. Compatibility
on lattice-preserving maps fixes the rational realization independently of a lattice.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.Scheme
