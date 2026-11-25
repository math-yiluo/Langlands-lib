/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.PointCount
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights

/-!
# Cohomology and the Euler series of a Weil representation

For an abelian sheaf `A` on the small étale site of a scheme `C`, ordinary étale cohomology
`Hⁱ(C, A) = RⁱΓ(C, A)` is Mathlib's `CategoryTheory.Sheaf.H` at the Grothendieck topology
`C.smallEtaleTopology`, and cohomology with proper support `H_cⁱ(C, A)` is
`AlgebraicGeometry.Etale.compactlySupportedCohomology`, with scoped notation `H_c(f)[A](i)`.
Neither is redefined here.

What is new in this file is the *Euler series* of a lisse Weil representation `ρ` on a curve
`p : C ⟶ Spec K` over a finite field, relative to an embedding `ι : ℚ̄_ℓ →+* ℂ`:

`L_ι(C₀, ρ, T) = ∏_{x ∈ |C₀|} ι P_x(ρ, T ^ e_x)⁻¹ ∈ 1 + T ℂ⟦X⟧`,

a product over the closed points of `C₀`, where `P_x(ρ, T)` is the local polynomial
`AlgebraicGeometry.WeilGroup.localPolynomial` and `e_x = p.degreeOver x` is the residue degree.
The product is locally finite: only finitely many factors contribute to a fixed coefficient,
since there are only finitely many closed points of bounded degree
(`AlgebraicGeometry.Scheme.Hom.finite_setOf_degreeOver_le`). Accordingly it is taken in the
product topology on `ℂ⟦X⟧`, for which `open scoped PowerSeries.WithPiTopology` supplies the
instances, and `AlgebraicGeometry.WeilGroup.multipliable_eulerFactors` records that it really
converges there, so that the `tprod` is not a junk value.

## Main definitions

- `AlgebraicGeometry.WeilGroup.eulerSeries` : the Euler series `L_ι(C₀, ρ, T)`.

## Main statements

- `AlgebraicGeometry.WeilGroup.multipliable_eulerFactors` : the Euler product converges.
- `AlgebraicGeometry.WeilGroup.constantCoeff_eulerSeries` : `L_ι(C₀, ρ, T) ∈ 1 + T ℂ⟦X⟧`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

open scoped PowerSeries.WithPiTopology

/-- The local factor `ι P_x(ρ, T ^ e_x)⁻¹` of the Euler series at a closed point `x`. -/
noncomputable def eulerFactor (x : C.finitePoints) : PowerSeries ℂ :=
  ((((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ p.degreeOver x.1) :
    Polynomial ℂ) : PowerSeries ℂ)⁻¹

variable {W l ρ} in
/-- The complex local polynomial takes the value `1` at `0`. -/
theorem eval_zero_map_localPolynomial (x : C.finitePoints) :
    ((W.localPolynomial l ρ x).map ι).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, localPolynomial,
    LinearMap.coeff_zero_charpolyRev, map_one]

variable {W l ρ} in
/-- The constant term of a local factor of the Euler series is `1`. -/
theorem constantCoeff_eulerFactor (x : C.finitePoints) :
    PowerSeries.constantCoeff (W.eulerFactor l ρ ι x) = 1 := by
  rw [eulerFactor, PowerSeries.constantCoeff_inv, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, zero_pow (p.degreeOver_ne_zero x.2),
    eval_zero_map_localPolynomial, inv_one]

/-- Blueprint `theorem-trace-formula-euler-product--1`: Cohomology and the Euler series.

The Euler product converges in the product topology of `ℂ⟦X⟧`: the local factor at `x` is
`1` modulo `T ^ e_x`, and only finitely many closed points have degree below a given bound
(`AlgebraicGeometry.Scheme.Hom.finite_setOf_degreeOver_le`), so only finitely many factors
contribute to a fixed coefficient. -/
theorem multipliable_eulerFactors : Multipliable (W.eulerFactor l ρ ι) := by
  refine PowerSeries.WithPiTopology.multipliable_inv_of_X_pow_dvd_sub_one
    (e := fun x : C.finitePoints ↦ p.degreeOver x.1) (fun x ↦ p.degreeOver_ne_zero x.2)
    (fun x ↦ ?_) p.finite_setOf_degreeOver_le
  set P := (W.localPolynomial l ρ x).map ι
  obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_iff.2 (show (P - 1).coeff 0 = 0 by
    rw [Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_zero_eq_eval_zero,
      eval_zero_map_localPolynomial, sub_self])
  have h : P.comp (Polynomial.X ^ p.degreeOver x.1) - 1 =
      Polynomial.X ^ p.degreeOver x.1 * Q.comp (Polynomial.X ^ p.degreeOver x.1) := by
    rw [← Polynomial.one_comp (p := Polynomial.X ^ p.degreeOver x.1), ← Polynomial.sub_comp, hQ,
      Polynomial.mul_comp, Polynomial.X_comp]
  refine ⟨(Q.comp (Polynomial.X ^ p.degreeOver x.1) : PowerSeries ℂ), ?_⟩
  have h' := congrArg (fun q : Polynomial ℂ ↦ (q : PowerSeries ℂ)) h
  simpa only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_X] using h'

/-- Blueprint `theorem-trace-formula-euler-product--1`: Cohomology and the Euler series.

The Euler series `L_ι(C₀, ρ, T) = ∏_{x ∈ |C₀|} ι P_x(ρ, T ^ e_x)⁻¹` of a Weil representation
`ρ`, the locally finite product over the closed points `x` of the curve of the inverses of the
local polynomials `P_x(ρ, T)` of `AlgebraicGeometry.WeilGroup.localPolynomial`, transported to
`ℂ` along `ι` and substituted into `T ^ e_x` for the residue degree `e_x = p.degreeOver x`.

Each factor is a formal power series with constant term `1`, so the product lies in
`1 + T ℂ⟦X⟧` (`AlgebraicGeometry.WeilGroup.constantCoeff_eulerSeries`); it is taken in the
product topology on `ℂ⟦X⟧`, in which it converges by
`AlgebraicGeometry.WeilGroup.multipliable_eulerFactors`. -/
noncomputable def eulerSeries : PowerSeries ℂ :=
  ∏' x : C.finitePoints, W.eulerFactor l ρ ι x

/-- Blueprint `theorem-trace-formula-euler-product--1`: Cohomology and the Euler series.

The Euler series lies in `1 + T ℂ⟦X⟧`: every local factor has constant term `1`, because the
local polynomial `P_x(ρ, T) = det (1 - T F_x)` does. -/
theorem constantCoeff_eulerSeries :
    PowerSeries.constantCoeff (W.eulerSeries l ρ ι) = 1 := by
  have h := (W.multipliable_eulerFactors l ρ ι).hasProd.map (PowerSeries.constantCoeff (R := ℂ))
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℂ)
  simp only [Function.comp_def, constantCoeff_eulerFactor] at h
  exact h.unique hasProd_one

end WeilGroup

end AlgebraicGeometry
