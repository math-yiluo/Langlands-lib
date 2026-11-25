/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

/-!
# Definitions: the zeta function of a scheme over a finite field

This file provides the definitions shared by the `leanprover/comparator`
challenge/solution pair in this directory (see `Challenge.lean` and `Solution.lean`).
It only imports mathlib.

For a scheme `X` over a finite field `k` with `q` elements, given by a structure morphism
`f : X ⟶ Spec k`, the zeta function of `X` is the formal power series

`Z(X, t) = exp (∑ N_n * t ^ n / n)`,

where `N_n = #X(𝔽_(q ^ n))` is the number of points of `X` with values in the degree `n`
extension of `k`. The Weil conjectures predict a factorization of `Z(X, t)` into integral
polynomials satisfying a functional equation and an analogue of the Riemann hypothesis;
the three predicates spelling this out are also defined here.

## Main definitions

- `FiniteField.galoisExtension k n`: a model of the degree `n` extension of the finite
  field `k`, as the splitting field of `X ^ (#k ^ n) - X`.
- `AlgebraicGeometry.Scheme.Hom.fieldPoints`: the `K`-rational points of `X` relative to a
  structure morphism `f : X ⟶ Spec k`.
- `AlgebraicGeometry.Scheme.Hom.pointCount`: the number `N_n` of points of `X` rational
  over the degree `n` extension of `k`.
- `AlgebraicGeometry.Scheme.Hom.zetaSeries`: the power series `Z(X, t) ∈ ℚ⟦t⟧`.
- `AlgebraicGeometry.IsWeilFactorization`: the factorization of `Z(X, t)` predicted by the
  rationality conjecture.
- `AlgebraicGeometry.WeilFunctionalEquation`: the functional equation, as a correspondence
  of root multisets.
- `AlgebraicGeometry.WeilRiemannHypothesis`: the Riemann hypothesis for the roots.

## References

- [J.-P. Serre, *Zeta and L functions*][serre1965]
- [A. Weil, *Numbers of solutions of equations in finite fields*][weil1949]
-/

universe u

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace FiniteField

/-- A model for the degree `n` extension of a finite field `k` with `q` elements:
the splitting field of `X ^ (q ^ n) - X` over `k`. For infinite `k` this is junk
(the polynomial degenerates), as is the value for `n = 0`. -/
def galoisExtension (k : Type u) [Field k] (n : ℕ) : Type u :=
  (X ^ Nat.card k ^ n - X : k[X]).SplittingField
deriving Field, Algebra k, FiniteDimensional k

instance instIsSplittingFieldGaloisExtension (k : Type u) [Field k] (n : ℕ) :
    IsSplittingField k (galoisExtension k n) (X ^ Nat.card k ^ n - X) :=
  inferInstanceAs (IsSplittingField k (X ^ Nat.card k ^ n - X : k[X]).SplittingField
    (X ^ Nat.card k ^ n - X))

end FiniteField

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- The `K`-rational points `X(K)` of a scheme `X` with structure morphism
`f : X ⟶ Spec k`, for a field extension `K` of `k`: morphisms `Spec K ⟶ X` commuting
with the structure morphisms. -/
def Hom.fieldPoints (f : X.Hom (Spec (.of k))) (K : Type u) [Field K] [Algebra k K] :
    Type u :=
  {g : Spec (.of K) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))}

/-- `f.pointCount n` is the number `N_n` of points of `X` which are rational over the
degree `n` extension of `k`, with junk value `0` if this number is infinite. -/
noncomputable def Hom.pointCount (f : X.Hom (Spec (.of k))) (n : ℕ) : ℕ :=
  Nat.card (f.fieldPoints (FiniteField.galoisExtension k n))

/-- The zeta function of a scheme `X` over a finite field `k` with `q` elements, given by
a structure morphism `f : X ⟶ Spec k`, as a formal power series:
`Z(X, t) = exp (∑ N_n * t ^ n / n)` where `N_n = #X(𝔽_(q ^ n))`.

It is related to the zeta function `ζ_X` of `X` as an abstract scheme by the formal
identity `ζ_X(s) = Z(X, q ^ (-s))`. -/
noncomputable def Hom.zetaSeries (f : X.Hom (Spec (.of k))) : PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst
    (PowerSeries.mk fun n ↦ if n = 0 then 0 else (f.pointCount n : ℚ) / n)

end AlgebraicGeometry.Scheme

end

namespace AlgebraicGeometry

/-- `IsWeilFactorization q d Z P` says that the polynomials `P₀, …, P_{2d} ∈ ℤ[t]`
factor the power series `Z` as `Z = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})`, normalized by
`Pᵢ(0) = 1`, with `P₀ = 1 - t` and `P_{2d} = 1 - qᵈ t`. This is the shape of the zeta
function of a smooth, proper, geometrically integral scheme of dimension `d` over a field
with `q` elements predicted by the Weil conjectures. -/
structure IsWeilFactorization (q d : ℕ) (Z : PowerSeries ℚ)
    (P : Fin (2 * d + 1) → Polynomial ℤ) : Prop where
  coeff_zero_eq_one : ∀ i, (P i).coeff 0 = 1
  apply_zero : P 0 = 1 - Polynomial.X
  apply_last : P (Fin.last (2 * d)) = 1 - Polynomial.C ((q : ℤ) ^ d) * Polynomial.X
  factorization : Z * ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
      ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) =
    ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
      ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)

/-- The functional equation part of the Weil conjectures: `α ↦ qᵈ / α` maps the inverse
roots of `Pᵢ` bijectively (with multiplicity) to the inverse roots of `P_{2d - i}`.
In terms of the complex roots `z = 1 / α` this says that `z ↦ 1 / (qᵈ z)` identifies the
root multisets of `Pᵢ` and `P_{2d - i}`. It implies the classical functional equation
`Z(X, 1 / (qᵈ t)) = ± q^{dχ/2} tᵡ Z(X, t)` for the associated rational function. -/
def WeilFunctionalEquation (q d : ℕ) (P : Fin (2 * d + 1) → Polynomial ℤ) : Prop :=
  ∀ i, ((P i.rev).map (Int.castRingHom ℂ)).roots =
    (((P i).map (Int.castRingHom ℂ)).roots.map fun z ↦ ((q : ℂ) ^ d * z)⁻¹)

/-- The Riemann hypothesis part of the Weil conjectures: every inverse root of `Pᵢ` has
absolute value `q^{i/2}`, i.e. every complex root `z` of `Pᵢ` satisfies `‖z‖ = q^{-i/2}`. -/
def WeilRiemannHypothesis (q d : ℕ) (P : Fin (2 * d + 1) → Polynomial ℤ) : Prop :=
  ∀ i : Fin (2 * d + 1), ∀ z ∈ ((P i).map (Int.castRingHom ℂ)).roots,
    ‖z‖ = (q : ℝ) ^ (-(i.1 : ℝ) / 2)

end AlgebraicGeometry
