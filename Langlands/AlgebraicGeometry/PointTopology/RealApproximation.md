# Elementary real approximation for affine schemes

`HasRealApproximation X` means that the actual map `X(ℚ) → X(ℝ)` induced by
`ℚ → ℝ` has dense range for the Library's evaluation topology. The scheme
`X` is affine over `ℚ`; this definition imposes no group structure.

This internal supporting development provides the following elementary tools.

- `HasRealApproximation.map` transports density through an actual scheme
  morphism whose map on real points is surjective. Continuity is the published
  affine-scheme functoriality theorem. Compatibility with coefficient change
  follows from associativity of composition in the over category.
- `HasRealApproximation.of_iso` applies this result to a scheme isomorphism.
- `HasRealApproximation.tensor` proves approximation for a product of two
  affine schemes locally of finite type over `ℚ`. The product of the two dense
  coefficient-change maps is dense. The actual categorical pairing is continuous
  by the published point-topology product theorem and surjective by the two
  projections. Pairing commutes with precomposition.
- `spectrumAlgebraPointEquiv_changeRing_real` identifies coefficient change
  with postcomposition of the algebra map. Its proof uses the contravariance
  of `Spec.preimage`.
- `hasRealApproximation_polynomialSpectrum` identifies polynomial-ring points
  with their generator values. Coordinatewise rational inclusion has dense range
  by Mathlib's `Rat.denseRange_cast` and `DenseRange.piMap`. The direct spectrum
  comparison commutes with coefficient change, so the inverse real-coordinate
  homeomorphism transports this density to actual points.
- `hasRealApproximation_affineSpace` transports the preceding result through
  Mathlib's actual polynomial-spectrum isomorphism over `Spec ℚ`.

The polynomial and affine-space assertions allow any index type in `Type`,
including an empty index type. The product assertion retains the local
finite-type hypotheses needed by the imported continuity theorem.

## Internal provenance

These are elementary consequences of the published evaluation topology and
Mathlib's rational density and product topology results. They supply the
topological step of real approximation independently of the group structure
theorems and do not assert real approximation for an arbitrary affine scheme.
In particular, the map lemma explicitly assumes surjectivity on actual real
points.
