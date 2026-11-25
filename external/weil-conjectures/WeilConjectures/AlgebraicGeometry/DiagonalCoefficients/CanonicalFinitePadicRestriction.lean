/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface

/-! # Finite scalar restriction in the realization's coefficient category -/

/- Repair note: this source is included with its new DAG node so the interface packet
   carries the declaration and its recorded lean.file together. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The specified finite-to-integral restriction, with the ring structure supplied
by the commutative coefficient ring, as in `FiniteRealization`.

Source: coefficient changes (1), restriction along the positive residue projection.
(blueprint: def-canonical-finite-padic-restriction).
The functor is the original restriction itself. Naming this view shares the same
coefficient-category and localization instances in successive derived functors. -/
abbrev canonicalFinitePadicRestriction
    (l n : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X)
        (@ModuleCat.{u + 1} (diagonalResidue.{u} l n)
          (inferInstance : CommRing (diagonalResidue.{u} l n)).toRing) ⥤
      DiagonalMod l X :=
  diagonalFiniteToPadic l n X

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
