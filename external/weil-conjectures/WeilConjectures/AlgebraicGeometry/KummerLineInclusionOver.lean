/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerLineGeometry

/-!
# The punctured-line inclusion is over the base field

Source: blueprint `prop-pur-gm-relative-kummer`, Step 2, final paragraph, the
factorization π = pj, with the field models of `def-pur-kummer-line-geometry`
(blueprint: lem-pur-kummer-line-inclusion-over).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The polynomial-to-Laurent inclusion commutes with the structure maps to `Spec k`.

Source: blueprint `prop-pur-gm-relative-kummer`, Step 2, final paragraph, π = pj
(blueprint: lem-pur-kummer-line-inclusion-over).

Proof: write `u : k[t] → k[t,t⁻¹]` for the polynomial-to-Laurent map and `c_P`, `c_L`
for the respective constant maps from `k`. The image under `u` of `c_P(a)` has coefficient
`a` at exponent zero and zero at every other exponent, including negative exponents.
Thus `u(c_P(a)) = c_L(a)` for every `a`, including zero. Extensionality gives
`u ∘ c_P = c_L`. By the defining formulas for `KummerLine.inclusion` and
`KummerLine.structureMap`, contravariant functoriality of `Spec` identifies the left
side of the asserted equation with `Spec(u ∘ c_P)`. Substitution gives `Spec(c_L)`,
which is the structure map of the punctured line. -/
theorem normalizedKummerInclusion_over (k : Type u) [Field k] :
    KummerLine.inclusion k ≫ KummerLine.structureMap k false =
      KummerLine.structureMap k true := by
  have h : (Polynomial.toLaurent (R := k)).comp Polynomial.C = LaurentPolynomial.C := by
    apply RingHom.ext
    intro a
    exact Polynomial.toLaurent_C a
  simp only [KummerLine.inclusion, KummerLine.structureMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h]

end AlgebraicGeometry.Etale
