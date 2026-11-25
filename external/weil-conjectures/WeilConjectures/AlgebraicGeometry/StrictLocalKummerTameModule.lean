/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Strict-local compatible-root tameness

Source: the strict-local tame condition in paragraph (3) of the direct-image proof,
blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability.
(blueprint: def-sfb-strict-local-kummer-tame-module).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Positive root orders prime to the residue characteristic.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
abbrev TameRootOrder (p : ℕ) := {n : ℕ // 0 < n ∧ n.Coprime p}

/-- Equations for all roots, with compatibility under divisibility. These impose both
x_(i,n)^n = t_i and x_(i,m)^(m/n) = x_(i,n) whenever n divides m.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
def tameRootRelations (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) :
    Set (MvPolynomial (Fin r × TameRootOrder p) R) :=
  {a | (∃ (i : Fin r) (n : TameRootOrder p),
      a = MvPolynomial.X (i, n) ^ n.val - MvPolynomial.C (t i)) ∨
    ∃ (i : Fin r) (n m : TameRootOrder p), n.val ∣ m.val ∧
      a = MvPolynomial.X (i, m) ^ (m.val / n.val) - MvPolynomial.X (i, n)}

/-- The actual algebra adjoining compatible roots of the parameters of every order prime to p.
Its spectrum over the boundary complement is the inverse-limit Kummer cover. In rank zero
there are no variables or relations, giving the original ring canonically.
Source: tame-boundary comparison, strict-local condition
(blueprint: def-sfb-strict-local-kummer-tame-module). -/
abbrev tameRootAlgebra (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) :=
  MvPolynomial (Fin r × TameRootOrder p) R ⧸ Ideal.span (tameRootRelations p t)

end AlgebraicGeometry.ProEtale
