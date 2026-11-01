# Cancelling determinant density for the actual GL Haar measure

This internally derived prerequisite proves integrability and Bochner integral
formulas for the natural matrix-size determinant power, using the actual general
linear Haar measure. It retains the supplied additive measure restricted to the
invertible locus, and retains one strictly positive finite Haar-normalization
scalar. It also proves genuine joint convergence and Fubini for a comparison-box
integrand on the actual unipotent group times GL. All declarations belong to
`Langlands.RankinSelberg.GLDeterminantDensity`.

## Algebraic cancellation

For a field `K`, a natural matrix size `r`, and a zero-preserving multiplicative
map `χ : K →*₀ ℝ≥0`, the definition is

```text
forwardWeight r χ X = χ(det X)^r.
```

The imported `matrixWeight` is `χ(det X)⁻¹^r`.
`matrixWeight_mul_forwardWeight` proves that their product is one on the actual
invertible matrices. The proof uses that the image under `χ` of a unit is a unit.
There is no cancellation claim at singular matrices.

## General measure formulas

The general section assumes a Hausdorff topological division field, with Borel
measurable structures on the square matrices and on `GL_r(K)`, and continuous
`χ`. Put `U = range Units.val`, the open invertible locus. Let `μ` be any measure
on matrices, `η` a measure on GL, and `c : ℝ≥0` with `0 < c`. The explicit
comparison hypothesis is

```text
weightedRestriction r χ μ = c • η.
```

The weighted restriction is the measure from the imported GLDensity module:
comap of `μ` along the actual matrix inclusion, with the inverse determinant
density. For an arbitrary function `A` into a real normed vector space,
`integrable_forwardWeight_iff_of_eq_smul` and
`integral_forwardWeight_of_eq_smul` prove

```text
Integrable (g ↦ forwardWeight r χ g.val • A(g.val)) η
  ↔ Integrable A (μ.restrict U),

∫ g, forwardWeight r χ g.val • A(g.val) ∂η
  = c⁻¹ • ∫ X, A(X) ∂μ.restrict U.
```

The integral equality uses totalized Bochner integrals and assumes no
integrability of `A`; the separate equivalence supplies the convergence claim.
The scalar depends on the comparison of measures, rather than on `A`.
The proof uses the imported weighted-restriction transport formulas, cancellation
almost everywhere on `μ.restrict U`, and inversion of the nonzero scalar `c`.

The product versions
`integrable_prod_forwardWeight_iff_of_eq_smul` and
`integral_prod_forwardWeight_of_eq_smul` allow any measurable auxiliary space `H`
with measure `μH`, and assume `SFinite μH`, `SFinite μ`, and `SFinite η`. For any
`A : H × M_r(K) → E` they prove

```text
Integrable ((h,g) ↦ forwardWeight r χ g.val • A(h,g.val)) (μH.prod η)
  ↔ Integrable A (μH.prod (μ.restrict U)),

∫ (h,g), forwardWeight r χ g.val • A(h,g.val) ∂μH.prod η
  = c⁻¹ • ∫ z, A(z) ∂μH.prod (μ.restrict U).
```

Here the proof pushes the actual product measure along `(h,g) ↦ (h,g.val)`.
The result is the product restricted matrix measure with density
`matrixWeight r χ` in the second variable. The with-density integrability and
integral formulas cancel that density almost everywhere. The stated s-finiteness
hypotheses justify product transport and projection of the almost-everywhere
invertibility property. These statements concern joint convergence, with no
inference from convergence of an averaged integral.

## Canonical p-adic specialization

For every prime `p` and `F : PadicField p`, the section installs the canonical
topology, valuation, nonarchimedean local-field structure, Hausdorffness,
countability, sigma compactness, and Borel structures. The canonical GL and
unipotent local-compactness certificates supply the Haar instances.
Write `abv = normalizedAbsoluteValue F.canonicalTopologicalData` and take `χ`
to be the canonical `normalizedAbsHom`.

For every supplied scalar additive Haar measure `ν` and natural `n`,
`rectangularHaarScalar F ν n` chooses the scalar from the published p-adic
GLDensity comparison for the exact measure
`rectangularMeasure ν (n+1) (n+1)`. Its positivity and equality lemmas prove

```text
0 < rectangularHaarScalar F ν n,
weightedRestriction (n+1) χ (rectangularMeasure ν (n+1) (n+1))
  = rectangularHaarScalar F ν n • generalLinearHaar F.Carrier n.
```

This NNReal scalar is finite, fixed independently of every test, function,
character, and auxiliary measure. Its value is not asserted to be one.

`forwardWeight_eq_determinantWeight` identifies its complex action with
`determinantWeight abv g (n+1 : ℕ) * z`; the natural exponent is coerced to
`ℂ`. The proof uses the natural-exponent identity for complex powers.
Consequently `integrable_generalLinearHaar_natWeight_iff` and
`integral_generalLinearHaar_natWeight` give the preceding single-variable
formulas with the actual GL Haar measure, this same rectangular measure, and
complex scalar `((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹`.
The product versions
`integrable_prod_generalLinearHaar_natWeight_iff` and
`integral_prod_generalLinearHaar_natWeight` give the same conclusions with any
s-finite auxiliary measure. All these results allow `n = 0`.

## Actual unipotent and GL product convergence

Let `ψ : UnitaryAdditiveCharacter F.Carrier`, and let `Φ₁, Φ₂` be
Schwartz–Bruhat functions on square matrices of size `n+1`. Suppose

```text
tsupport Φ₂ ⊆ RankOneBox.box F A q a,   0 < a,
```

where `A,q : ℤ` and `a : ℕ`. For any continuous complex function `b` on the
full matrix space, `integrable_unipotent_box_generalLinear_natWeight` proves
integrability, for `unipotentHaar.prod generalLinearHaar`, of the function

```text
(u,g) ↦ determinantWeight abv g (n+1 : ℕ)
        * ((standardCharacter ψ n u)⁻¹).val
        * Φ₁(u.val.val * g.val) * Φ₂(g.val) * b(g.val),
```

with the determinant factor grouped outside the product of the four remaining
factors, as in the Lean declaration. There is no invertible-support hypothesis
on `Φ₁`. The proof takes the full additive-matrix product integrability from
the published FramedIntegrability module, restricts its second measure to `U`,
and applies the canonical product cancellation equivalence.

`integral_unipotent_box_generalLinear_natWeight_swap` exchanges the two iterated
integrals of precisely this function by Fubini and the proved joint convergence.
It uses the actual unipotent and GL Haar measures without rescaling them and
works also for `n = 0`.

The character type bundles nontriviality. These support and measure arguments
use its continuity, without using the nontriviality field or assuming
self-duality of `ν`. The full-matrix weight `b` is explicitly continuous; no
continuity of arbitrary determinant powers across the singular locus is claimed.

## Provenance and scope

This is an internal derivation from the published GLDensity transport and Haar
comparison, the published FramedIntegrability box bound, and the existing
normalized determinant and canonical measure definitions. Mathlib supplies
measurable product transport, with-density identities, scalar measure identities,
almost-everywhere projection and Fubini. No original-literature functional
equation is used as a premise.

The additive measure stays restricted to the actual invertible locus in every
cancellation formula. No assertion about the measure of singular matrices is
made. This module supplies a measure and convergence prerequisite; it does not
prove the Fourier endpoint, construct its common coefficient and test, or prove
the final gamma functional-equation comparison.
