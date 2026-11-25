/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface

/-! # The residue Cartier Kummer Chern equation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The positive residue Cartier class satisfies the geometric Chern equation.

Source: Cartier reduction and site comparison; supported Kummer Chern realization.
(blueprint: lem-sfb-diagonal-trace-supported-finite-boundary-cartier-kummer).

Proof: apply cartier_reduction_site_comparison to the residue ring at positive
exponent n+1 and the diagonal Cartier immersion. Its geometric Chern clause is
exactly this assertion. The residue ring is finite because l is prime. The site
comparison theorem proves the clause by identifying the uniquely reduced class
with the ordinary supported Kummer class, applying supported Kummer Chern
realization, and transporting along the canonical source comparison. -/
theorem diagonalTrace_supportedFiniteBoundary_cartierKummer
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤))) (n : ℕ) :
    GeoCartierChernEquation (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y)
      (diagonalImmersion_cartier Y) (diagonalSurface_power_unit l Y hY n)
      (cartierResidueReducedPro l (Fact.out : l.Prime) (n + 1)
        (diagonalImmersion Y) (diagonalImmersion_cartier Y)
        (diagonalSurface_power_unit l Y hY n)) := by
  let : Finite (diagonalResidue.{u} l n) :=
    cartierResidue_finite l (Fact.out : l.Prime) (n + 1)
  have h := cartier_reduction_site_comparison l (Fact.out : l.Prime) (n + 1)
    (Nat.succ_pos n) (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1))
    (diagonalImmersion Y) (diagonalImmersion_cartier Y)
    (diagonalSurface_power_unit l Y hY n)
  simpa only [cartierResidueReducedPro] using h.2.2.2.2.2.2.2.2.2.1

end AlgebraicGeometry.ProEtale.DiagonalTrace
