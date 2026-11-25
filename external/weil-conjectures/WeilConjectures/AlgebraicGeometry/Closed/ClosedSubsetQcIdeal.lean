/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Closed subsets are cut out by quasi-coherent ideals

Source: Stacks Project, Schemes, Lemma 26.12.4 (Tag 01J3), construction in its proof
(blueprint: lem-sc-closed-subset-qc-ideal).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every closed subset of a scheme is the vanishing locus of a quasi-coherent ideal sheaf.
Quasi-coherent ideal sheaves `𝒥 ⊆ 𝒪_Y` are Mathlib's `Y.IdealSheafData` (compatible affine-local
ideals with `I(D(f)) = I(U)_f`), and the vanishing set `V(𝒥) = {y : 𝒥_y ≠ 𝒪_{Y,y}}` is its
`support`.

Source: Stacks Project, Schemes, Lemma 26.12.4 (Tag 01J3), proof
(blueprint: lem-sc-closed-subset-qc-ideal).

Proof: Apply `lem-weil-pbc-reduced-induced-closed-subscheme` to the scheme and the closed
subset. Its vanishing ideal is quasi-coherent and on each affine open `Spec R` is the
radical ideal `I` with `V(I)` equal to the prescribed closed subset on that open. At the
point corresponding to a prime `p`, its stalk is `I_p` inside `R_p`; this equals `R_p`
exactly when `I` is not contained in `p`. Thus the vanishing set of this ideal is exactly
the prescribed subset. Take this vanishing ideal as `J`. -/
theorem exists_idealSheafData_support_eq (Y : Scheme.{u}) (Z : Set Y) (hZ : IsClosed Z) :
    ∃ J : Y.IdealSheafData, (J.support : Set Y) = Z := by
  exact ⟨IdealSheafData.vanishingIdeal ⟨Z, hZ⟩,
    IdealSheafData.coe_support_vanishingIdeal ⟨Z, hZ⟩⟩

end AlgebraicGeometry.Scheme
