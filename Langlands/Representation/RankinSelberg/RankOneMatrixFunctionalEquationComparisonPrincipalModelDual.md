# Signed principal dual pairing for actual coefficient-model vectors

This internal derived module extends the compact pairing to the actual
coefficient model of a smooth representation. The representation carrier
universe is independent of the p-adic field universe. The original
representation need not be irreducible, admissible, finitely generated, or
of Whittaker type for this conditional identity; smoothness suffices. The
functional may be any standard-character functional, including zero. The
two actual weighted integrability hypotheses are retained explicitly.

For `m ≥ 0`, the group is `GL_(m+2)`, the scalar group is the actual `GL_1`,
and the complementary rectangular block has size `m × 1`. Fix the arbitrary
supplied nontrivial unitary additive character `psi` and supplied self-dual
additive Haar measure `nu`. Choose `a > 0` with `q+a ≥ 0`, where `q` is the
conductor of `psi`, and put

```text
Psi = boxLatticeTest F (q+a) q a,
C = boxExtractionConstant F (n := m+1) (q+a) q a,
mu = principalAveragingMeasure F (n := m+1) a C.
```

The box and the principal measure are independent of the spectral exponent.
The scalar measure is `glOneMeasure F (m+1)`, with its actual density
`|det g|^(-(m+1))` relative to `GL_1` Haar. The complementary measure is the
actual `rectangularMeasure nu m 1`, and the full product is bracketed as
`mu × (glOneMeasure × rectangularMeasure)`.

The definition `principalModelFourierIntegrand F psi nu m a s W` is

```text
(|det h|^s W(h)) Fourier(Psi)(signedWeyl h).
```

The Fourier transform uses the plus entry-product pairing for the same
`psi` and `nu`. The definition `principalModelBlockIntegrand F m s W` is

```text
|det g|^s W(blockMatrixAt m 0 g Z · signedBlockWeyl · inverseTranspose(k)).
```

Here the point is exactly `principalSignedBlockPoint` from PrincipalCompactDual.
Both signed Weyl representatives and the averaging parameter are retained
literally. The module makes no unsigned sign conversion or identification
with a dual-model function.

The theorem `principalModelDual_pairing` states that the integral of the first
integrand equals the full product integral of the second, for every actual
`glModelFunction` of the supplied smooth representation and every complex
`s`, provided both displayed integrands are genuinely integrable for these
measures. The right-side premise concerns the full product, before averaging
in `k` or integrating the block; convergence of a possibly cancelling average
is insufficient and is not used. The theorem asserts no additional scalar.

The proof first establishes continuity of the literal block evaluation map.
Appending identity blocks is continuous by iteration of the continuous rank
inclusion. The rectangular unipotent has continuous value and explicit
inverse. After substituting the natural-number rank equality in
`blockMatrixAt`, their product is the actual block matrix; multiplication by
the fixed signed block Weyl and inverse transpose of the parameter preserves
continuity. Canonical Borel structures then give the measurable map needed
by compact approximation.

For every compact induced function, the hypothesis required by
`weighted_glModel_integral_eq_of_compact` follows from
`principalCompactDual_pairing_weighted`. On the left its fixed weight is
`|det h|^s Fourier(Psi)(signedWeyl h)`, with the group point `h`; on the right
its fixed weight is `|det g|^s`, with the literal block point above. A
pointwise associativity and commutativity identity puts the integrands into
this weighted-evaluation form. The compact approximation theorem then uses
the smooth coefficient-model inclusion and dominated convergence, with the
two supplied weighted bounds. The implemented proof does not assume a
matrix functional equation, a gamma equation, or a model equivalence.

The provenance is source-free composition of the cited compact principal
pairing and published weighted model approximation APIs, together with
continuity of existing group maps. Supplying the two bounds from matrix
analytic data and the actual original model vector, converting the signed
block expression into the Library dual integral, and proving the final
analytic, quotient-measure and functional transports remain separate work.
This supporting result does not complete the host gamma-comparison task.
