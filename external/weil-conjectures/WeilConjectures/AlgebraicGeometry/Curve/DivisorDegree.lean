/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.EffectiveDivisorCount
public import WeilConjectures.PointCount

/-!
# The degree of the line bundle of an effective divisor

Let `X` be a smooth proper curve over a field `k` and `E = ∑_P n_P [P]` an effective divisor on
`X`, with invertible ideal sheaf `𝒪_X(-E) = ∏_P 𝓘_P^{n_P}`
(`AlgebraicGeometry.Scheme.Divisor.idealSheaf`). The degree of a line bundle is defined
cohomologically, `deg ℒ = χ(ℒ) - χ(𝒪_X)` (`AlgebraicGeometry.Scheme.Modules.degree`). This file
identifies the degree of `𝒪_X(E) = 𝒪_X(-E)^∨` with the degree of the divisor `E`:
`deg 𝒪_X(E) = ∑_P n_P [κ(P) : k]`, which over an algebraically closed field is the degree
`∑_P n_P` of `AlgebraicGeometry.Scheme.Divisor.degree`.

## Main statements

- `AlgebraicGeometry.Scheme.degreeOver_eq_one_of_isAlgClosed`: over an algebraically closed
  field, closed points of a scheme locally of finite type have degree one.
- `AlgebraicGeometry.Scheme.Divisor.degree_dual_toModules_idealSheaf`:
  `deg 𝒪_X(E) = ∑_P n_P [κ(P) : k]` (blueprint `theorem-riemann-roch-coherent-serre-duality--1`).
- `AlgebraicGeometry.Scheme.Divisor.degree_dual_toModules_idealSheaf_eq_degree`: over an
  algebraically closed field, `deg 𝒪_X(E) = deg E` (blueprint
  `theorem-riemann-roch-coherent-serre-duality--1`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Over an algebraically closed field `k`, a closed point `P` of a `k`-scheme locally of finite
type has degree one: its residue field is `k` (Nullstellensatz), so `P` is the image of the
`k`-rational point `AlgebraicGeometry.pointOfClosedPoint`. -/
theorem degreeOver_eq_one_of_isAlgClosed [IsAlgClosed k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] {P : X} (hP : IsClosed {P}) :
    (X ↘ Spec (.of k)).degreeOver P = 1 := by
  have h := Hom.degreeOver_eq_one_of_comp_eq_id (X ↘ Spec (.of k))
    (pointOfClosedPoint (X ↘ Spec (.of k)) P hP) (pointOfClosedPoint_comp _ _ _)
    ⟨⊥, Ideal.isPrime_bot⟩
  rwa [pointOfClosedPoint_apply] at h

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **The degree of the line bundle of an effective divisor.** Let `E = ∑_P n_P [P]` be an
effective divisor on a smooth proper curve `X` over `k`. The degree
`deg 𝒪_X(E) = χ(𝒪_X(E)) - χ(𝒪_X)` of its line bundle `𝒪_X(E) = 𝒪_X(-E)^∨`, where
`𝒪_X(-E) = ∏_P 𝓘_P^{n_P}`, is `∑_P n_P [κ(P) : k]`.

The χ-degree of `𝒪_X(E)` is `dim_k Γ(E, 𝒪_E)`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules`), and
`dim_k Γ(E, 𝒪_E) = ∑_P n_P [κ(P) : k]`
(`AlgebraicGeometry.Scheme.Divisor.finrankΓ_subschemeι_idealSheaf`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem Divisor.degree_dual_toModules_idealSheaf (E : closedPoints X →₀ ℕ) :
    (Divisor.idealSheaf E).toModulesᵛ.degree k =
      E.sum fun P n ↦ (n : ℤ) * (X ↘ Spec (.of k)).degreeOver P.1 := by
  rw [(Divisor.isInvertible_idealSheaf (X ↘ Spec (.of k)) E).degree_dual_toModules,
    Divisor.finrankΓ_subschemeι_idealSheaf, Finsupp.sum, Finsupp.sum]
  push_cast
  rfl

/-- **The degree of a line bundle agrees with the degree of divisors.** Let `E = ∑_P n_P [P]` be
an effective divisor on a smooth proper curve `X` over an algebraically closed field `k`. Then
the degree `deg 𝒪_X(E) = χ(𝒪_X(E)) - χ(𝒪_X)` of its line bundle `𝒪_X(E) = 𝒪_X(-E)^∨`, where
`𝒪_X(-E) = ∏_P 𝓘_P^{n_P}`, is the degree `deg E = ∑_P n_P` of `E` as a divisor
(`AlgebraicGeometry.Scheme.Divisor.degree`). In particular `deg 𝒪_X([P]) = 1` for a closed
point `P`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem Divisor.degree_dual_toModules_idealSheaf_eq_degree [IsAlgClosed k]
    (E : closedPoints X →₀ ℕ) :
    (Divisor.idealSheaf E).toModulesᵛ.degree k =
      Divisor.degree X (E.mapRange Nat.cast Nat.cast_zero) := by
  rw [degree_dual_toModules_idealSheaf, Divisor.degree_apply,
    Finsupp.sum_mapRange_index fun _ ↦ rfl]
  refine Finsupp.sum_congr fun P _ ↦ ?_
  rw [degreeOver_eq_one_of_isAlgClosed P.2, Nat.cast_one, mul_one]

end AlgebraicGeometry.Scheme
