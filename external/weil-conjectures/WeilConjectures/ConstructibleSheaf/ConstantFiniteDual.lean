/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.ConstructibleSheaf.ConstantModuleDual

/-! # Dual of a constant finite module sheaf

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`, coefficient dual argument.
(blueprint: lem-weil-pbc-constant-finite-dual)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

/-- Constant sheafification commutes with the coefficient dual of a finite module.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` docstring, finite presentation argument.

Proof: Since Λ is noetherian and M is finitely generated, choose a presentation
Λ^m → Λ^n → M → 0 with m,n finite. Exactness of constant sheafification gives the
corresponding cokernel presentation of M_X. Internal Hom into Λ_X sends this cokernel
to the kernel of the map from the dual of Λ_X^n to the dual of Λ_X^m. The dual of a
finite free constant sheaf is the corresponding finite free constant sheaf, by the
finite biproduct tensor-Hom adjunction and the unit constraint. The map between those
duals is the constant sheafification of the transposed presentation matrix: evaluation
on a basis vector gives exactly its matrix coefficients. Constant sheafification preserves
finite limits, so this kernel is the constant sheaf of the module kernel of the transpose.
Applying Hom_Λ(-,Λ) to the original presentation identifies that kernel with Hom_Λ(M,Λ).
Composing these kernel isomorphisms gives the asserted isomorphism. This also covers
M = 0, the zero coefficient ring, and the empty scheme.
(blueprint: lem-weil-pbc-constant-finite-dual) -/
theorem nonempty_constant_finite_dual_iso (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    Nonempty ((ihom ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj
      (𝟙_ _) ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (M →ₗ[Λ] Λ))) := by
  exact nonempty_constantModuleDualIso X M

end AlgebraicGeometry.Scheme
