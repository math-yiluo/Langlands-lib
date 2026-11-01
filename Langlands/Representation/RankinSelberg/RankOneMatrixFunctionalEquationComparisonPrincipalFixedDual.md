# Removing the principal parameter for a principal-fixed coefficient

This internal derived module removes the compact principal parameter from the
actual signed complementary-block formula when the function is right fixed by
that principal subgroup. It proves full product convergence from genuine
scalar/block convergence before computing the compact average. The only
resulting scalar is the mass of the original principal averaging measure.

The two declarations in `Langlands.Conductor` are algebraic and apply to every
field `K`. The theorem
`inverseTranspose_mem_principalCongruenceSubgroup` works for any subring `O`
and ideal `I` of `O`. It proves that the actual image in the field group of the
integral reduction kernel is preserved by the inverse-transpose automorphism.
The proof takes an integral lift of an element. Its inverse remains in the
reduction kernel. The entrywise principal condition for the transpose follows
by exchanging its two indices, since the identity matrix is symmetric.
Inverse transpose commutes with the coefficient map by its actual entry
formula and preservation of inverses. Mapping the new integral lift back gives
the required field-group membership. The specialization
`inverseTranspose_mem_principalLevelSubgroup` uses the existing valuation
integer ring and maximal-ideal power. Both results include level zero. They
assert membership, not a measure-transport theorem.

In the canonical p-adic setting, let `W` be any complex-valued group function
on `GL_(m+2)`, for `m ≥ 0`, with the right invariance

```text
W(h k) = W(h) for every k in principalLevelSubgroup at level a.
```

The definition `principalFixedBlockIntegrand F m s W` is

```text
|det g|^s W(blockMatrixAt m 0 g Z · signedBlockWeyl).
```

This uses the actual `m × 1` rectangle `Z`, the signed complementary block
Weyl representative, and the complex determinant power for the canonical
normalized absolute value. The scalar and block measure is
`glOneMeasure F (m+1) × rectangularMeasure nu m 1`. In particular the existing
inverse-modulus density in `glOneMeasure` remains present.

For any real `C`, the measure `mu = principalAveragingMeasure F a C` is finite
and supported almost everywhere on the actual principal subgroup. Inverse
transpose preserves that subgroup, so `principalModelBlockIntegrand`, which
retains `inverseTranspose(k)` as its final right factor, equals
`principalFixedBlockIntegrand` almost everywhere on the full product
`mu × (glOneMeasure × rectangularMeasure)`. This is
`principalModelBlockIntegrand_ae_of_fixed`. The function `W` is not replaced
by a different vector and no global identity between an arbitrary original
coefficient and an average is asserted.

The theorem `integrable_principalModelBlockIntegrand_of_fixed` starts from
genuine integrability of the displayed scalar/block integrand. Its product
with the constant function one is integrable because `mu` is finite. The
proved almost-everywhere identity then gives full parameter-product
integrability. No convergence inference is made from equality of totalized
integrals. For `C ≥ 0`, the theorem
`integral_principalModelBlockIntegrand_of_fixed` computes the full product
integral as `C` times the fixed scalar/block integral. The separated-product
Bochner integral identity and the existing exact mass formula suffice; this
value identity also holds without a convergence premise.

Finally, `principalFixedModelDual_pairing` applies these results to an actual
coefficient-model vector of a smooth representation, with independent field
and representation universes. Let `psi` be the arbitrary supplied nontrivial
unitary additive character, `nu` its supplied self-dual Haar measure, and
`q` its conductor. Assume `a > 0` and `q+a ≥ 0`. The same box test and constant
as in the principal compact pairing are used:

```text
Psi = boxLatticeTest F (q+a) q a,
C = boxExtractionConstant F (n := m+1) (q+a) q a.
```

If the actual model vector is fixed by this principal subgroup, its literal
signed-Weyl Fourier restriction is integrable, and its fixed signed block
restriction is integrable, the theorem proves

```text
integral_h (|det h|^s W(h)) Fourier(Psi)(signedWeyl h) dh
  = C · integral_(g,Z) |det g|^s
      W(blockMatrixAt m 0 g Z · signedBlockWeyl).
```

The proof obtains the full product bound above, invokes
`principalModelDual_pairing`, and substitutes the exact compact mass. The
scalar `C` is strictly positive by the existing box-volume theorem. The
Fourier transform, rectangular measure, and character are unchanged.

The provenance is source-free use of principal congruence entry formulas,
the actual inverse-transpose automorphism, and the preceding principal model
pairing and averaging APIs. This module still assumes the two indicated
analytic bounds. It does not derive them from matrix functional-equation
data, convert signed expressions to unsigned dual JPSS integrals, or prove
the host gamma comparison or quotient/functional transports.
