/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CurveEndpoints
public import WeilConjectures.WeilSheaf.LFunction
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# The Euler product of a middle extension on an affine curve

Let `X₀` be a smooth geometrically connected affine curve over `𝔽_q`, `j : U₀ ↪ X₀` a dense open
and `ℱ` a lisse Weil sheaf on `U₀`. The middle extension `j_* ℱ` (`definition-middle-extension`) is
a constructible Weil sheaf on `X₀`, and its `L`-function is the graded form of its compactly
supported cohomology (`proposition-weights-j-boundary-points`):

`∏_{x ∈ |X₀|} det (1 - F_x T ^ {e_x} ∣ (j_* ℱ)_x̄)⁻¹ = det (1 - F T ∣ H_c¹) / det (1 - F T ∣ H_c²)`.

This is the Euler-product form of the trace formula
(`AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk`) for the sheaf
`j_* ℱ` placed in degree zero, together with the vanishing of `H_cⁱ (X, j_* ℱ)` outside degrees
`1` and `2`: in negative degrees and above the dimension `2`
(`AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`), and in degree `0`,
where a compactly supported section of `j_* ℱ` vanishes
(`AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk_directImage`: the Euler
  product identity for the middle extension, coefficientwise.
-/

@[expose] public section

universe u

open CategoryTheory PowerSeries

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth affine curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]

namespace WeilSheaf

/-- The local polynomial of a Frobenius module on a zero space is `1`. -/
theorem _root_.FrobeniusModule.localPolynomial_eq_one {K : Type*} [Field K]
    (M : FrobeniusModule K) [Subsingleton M.carrier] : M.localPolynomial = 1 := by
  rw [FrobeniusModule.localPolynomial, LinearMap.charpolyRev,
    LinearMap.charpoly_eq_one_of_subsingleton, ← Polynomial.C_1, Polynomial.reverse_C]

/-- Blueprint `proposition-weights-j-boundary-points`: Graded Euler-product identity for a
middle extension.

Let `X₀` be a smooth geometrically connected affine curve, `j : U₀ ↪ X₀` a dense open
immersion and `ℱ` a lisse Weil sheaf on `U₀`. Then, as power series in `T`,

`∏_{x ∈ |X₀|} det (1 - F_x T ^ {e_x} ∣ (j_* ℱ)_x̄)⁻¹ = det (1 - F T ∣ H_c¹ (X, j_* ℱ)) /`
`  det (1 - F T ∣ H_c² (X, j_* ℱ))`,

the product over the closed points being locally finite: for every `n` and every finite set `s`
of closed points containing those of degree at most `n`, the coefficients of `T ^ n` of the
finite product over `s` and of the right-hand side agree.

This is the trace formula in its Euler-product form for the constructible sheaf `j_* ℱ` in
degree zero, whose compactly supported cohomology vanishes outside degrees `1` and `2`. -/
theorem coeff_prod_inv_localPolynomial_stalk_directImage (F : WeilSheaf k₀ l U) (hF : F.IsLisse)
    (n : ℕ) (s : Finset C.finitePoints)
    (hs : ∀ x : C.finitePoints, (C ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (((((WeilSheaf.directImage j).obj F).stalk x).localPolynomial.comp
        (Polynomial.X ^ (C ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial _) :
          (PadicAlgCl l)⟦X⟧)⁻¹) =
      coeff n ((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 1).localPolynomial *
        ((((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).localPolynomial :
          Polynomial _) : (PadicAlgCl l)⟦X⟧))⁻¹ : (PadicAlgCl l)⟦X⟧) := by
  set J := (WeilSheaf.directImage j).obj F
  have hS : ∀ i ∉ ({0, 1, 2} : Finset ℤ), Subsingleton (J.compactlySupportedCohomology i).carrier :=
    fun i hi ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      exact subsingleton_compactlySupportedCohomology_directImage j F hF (by omega)
  rw [coeff_prod_inv_localPolynomial_stalk J hS n s hs]
  have := subsingleton_compactlySupportedCohomology_directImage_zero j F hF
  congr 1
  have h0' : (J.compactlySupportedCohomology 0).frobeniusEnd.charpolyRev = 1 :=
    (J.compactlySupportedCohomology 0).localPolynomial_eq_one
  have hc (i : ℤ) : constantCoeff
      ((J.compactlySupportedCohomology i).frobeniusEnd.charpolyRev : (PadicAlgCl l)⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      LinearMap.coeff_zero_charpolyRev]
  rw [LinearMap.alternatingCharpolyRevProd, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, ite_eq_left Even.zero,
    ite_eq_right (by decide), ite_eq_left (by decide), pow_one,
    Polynomial.comp_X, Polynomial.comp_X, Polynomial.comp_X, h0', Polynomial.coe_one, one_mul,
    PowerSeries.inv_eq_iff_mul_eq_one
      (by rw [map_mul, PowerSeries.constantCoeff_inv, hc, hc]; simp),
    FrobeniusModule.localPolynomial, FrobeniusModule.localPolynomial]
  have key (a b : (PadicAlgCl l)⟦X⟧) (ha : constantCoeff a = 1) (hb : constantCoeff b = 1) :
      a * b⁻¹ * (a⁻¹ * b) = 1 := by
    calc a * b⁻¹ * (a⁻¹ * b) = (a * a⁻¹) * (b * b⁻¹) := by ring
      _ = 1 := by
        rw [PowerSeries.mul_inv_cancel _ (by rw [ha]; exact one_ne_zero),
          PowerSeries.mul_inv_cancel _ (by rw [hb]; exact one_ne_zero), one_mul]
  exact key _ _ (hc 1) (hc 2)

end WeilSheaf

end AlgebraicGeometry
