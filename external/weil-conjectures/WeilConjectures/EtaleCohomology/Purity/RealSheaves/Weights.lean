/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.ZetaFunction

/-!
# Local weights, reality and determinant weights

Let `ρ` be a lisse Weil representation on a curve `C₀ / 𝔽_q` and `ι : ℚ̄_ℓ →+* ℂ` a field
embedding. At a closed point `x` of `C₀` the local Frobenius `F_x` acts on the geometric
stalk, and the local polynomial is `P_x(ρ, T) = det (1 - T F_x)`. The `ι`-weight of a nonzero
local eigenvalue `α` is `2 log |ι α| / log q_x`.

This file defines these notions, punctual `ι`-purity, the bound `weights ≤ w`, `ι`-reality,
and the determinant weight `dw_ι(V) = wt_ι(det V) / rank V`.

The rank `N_γ` and the weight sum `B_γ` of `definition-determinant-weight--1` are sums over the
family of irreducible constituents of a semisimple Weil sheaf *counted with multiplicity*; they are
defined in `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights`
(`AlgebraicGeometry.WeilGroup.rankAbove`, `AlgebraicGeometry.WeilGroup.weightSumAbove`).

## Main definitions

- `AlgebraicGeometry.WeilGroup.frobeniusWeight` : the `ι`-weight `2 log |ι α| / log q_x` of a
  local Frobenius eigenvalue.
- `AlgebraicGeometry.WeilGroup.localPolynomial` : `P_x(ρ, T) = det (1 - T F_x)`.
- `AlgebraicGeometry.WeilGroup.localEigenvalues` : the multiset of local eigenvalues.
- `AlgebraicGeometry.WeilGroup.IsPunctuallyPure`, `HasWeightsAtMost`, `IsReal`.
- `AlgebraicGeometry.WeilGroup.HasDetWeight` : `dw_ι(ρ) = γ`.

## Main statements

- `AlgebraicGeometry.WeilGroup.localPolynomial_eq_charpolyRev_of_isConj` : the local
  polynomial only depends on the Frobenius conjugacy class.
- `AlgebraicGeometry.WeilGroup.localPolynomial_eq_prod_localEigenvalues` : the local
  polynomial is `∏_α (1 - α T)` over the local eigenvalues.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

/-- Blueprint `definition-weights`: Local weights and reality.

The `ι`-weight of a nonzero local eigenvalue `α`, relative to the residue cardinality `qₓ`:
`wt_{ι, qₓ}(α) = 2 log |ι α| / log qₓ`. -/
noncomputable def frobeniusWeight {E : Type*} [Field E] (ι : E →+* ℂ) (qx : ℕ) (α : E) : ℝ :=
  2 * Real.log ‖ι α‖ / Real.log qx

end WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V)

/-- Blueprint `definition-weights`: Local weights and reality.

The local polynomial `P_x(ρ, T) = det (1 - T F_x ∣ V)` of a Weil representation at a closed
point `x` of the curve. -/
noncomputable def localPolynomial (x : C.finitePoints) : Polynomial (PadicAlgCl l) :=
  (ρ (W.frobenius x)).charpolyRev

/-- Blueprint `definition-weights`: Local weights and reality.

The multiset of local Frobenius eigenvalues of `ρ` at a closed point `x`, the inverse roots of
`AlgebraicGeometry.WeilGroup.localPolynomial`; see
`AlgebraicGeometry.WeilGroup.localPolynomial_eq_prod_localEigenvalues`. -/
noncomputable def localEigenvalues (x : C.finitePoints) : Multiset (PadicAlgCl l) :=
  (ρ (W.frobenius x)).charpoly.roots

variable (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `definition-weights`: Local weights and reality.

`ρ` is punctually `ι`-pure of weight `w` if every local Frobenius eigenvalue at every closed
point has `ι`-weight `w`. -/
def IsPunctuallyPure (w : ℝ) : Prop :=
  ∀ (x : C.finitePoints), ∀ α ∈ W.localEigenvalues l ρ x,
    frobeniusWeight ι (C.pointNorm x.1) α = w

/-- Blueprint `definition-weights`: Local weights and reality.

`ρ` has weights at most `w` if every local Frobenius eigenvalue at every closed point has
`ι`-weight at most `w`. -/
def HasWeightsAtMost (w : ℝ) : Prop :=
  ∀ (x : C.finitePoints), ∀ α ∈ W.localEigenvalues l ρ x,
    frobeniusWeight ι (C.pointNorm x.1) α ≤ w

/-- Blueprint `definition-weights`: Local weights and reality.

`ρ` is `ι`-real if `ι P_x(ρ, T)` has real coefficients for every closed point `x`;
equivalently, every complex local eigenvalue multiset is stable under complex conjugation. -/
def IsReal : Prop :=
  ∀ (x : C.finitePoints) (n : ℕ), (starRingEnd ℂ) (ι ((W.localPolynomial l ρ x).coeff n)) =
    ι ((W.localPolynomial l ρ x).coeff n)

/-- Blueprint `definition-determinant-weight--1`: Determinant weights and weight blocks.

`ρ` has determinant weight `γ`, written `dw_ι(ρ) = γ`, if the determinant character is
punctually `ι`-pure of weight `rank ρ * γ`. By `theorem-rank-one-sheaves-have-finite` a nonzero
irreducible `ρ` has exactly one determinant weight. -/
def HasDetWeight (γ : ℝ) : Prop :=
  ∀ x : C.finitePoints,
    frobeniusWeight ι (C.pointNorm x.1) (LinearMap.det (ρ (W.frobenius x)))
      = Module.finrank (PadicAlgCl l) V * γ

variable {W l ρ}

/-- Blueprint `situation-weil`: Local Frobenius polynomials.

The local polynomial at `x` is `det (1 - T ρ g ∣ V)` for *every* member `g` of the
Frobenius conjugacy class of degree `e_x` supplied by `x`: a characteristic polynomial is
invariant under conjugation, so the local polynomial of `definition-weights` is well defined
and is computed by the representation of `definition-weil-representation--1`. -/
theorem localPolynomial_eq_charpolyRev_of_isConj {x : C.finitePoints} {g : W.carrier}
    (hg : IsConj (W.frobenius x) g) :
    W.localPolynomial l ρ x = (ρ g).charpolyRev :=
  LinearMap.charpolyRev_of_isConj (ρ.map_isConj hg)

/-- Blueprint `definition-weights`: Local weights and reality.

The local polynomial is the product `∏_α (1 - α T)` over the local eigenvalues: `ℚ̄_ℓ` is
algebraically closed, so the characteristic polynomial of `F_x` splits as `∏_α (X - α)`, and
`AlgebraicGeometry.WeilGroup.localPolynomial` is its reverse. This is what makes the local
eigenvalues the inverse roots of the local polynomial. -/
theorem localPolynomial_eq_prod_localEigenvalues (x : C.finitePoints) :
    W.localPolynomial l ρ x =
      ((W.localEigenvalues l ρ x).map fun α ↦ 1 - Polynomial.C α * Polynomial.X).prod :=
  LinearMap.charpolyRev_eq_prod_roots _

end WeilGroup

end AlgebraicGeometry
