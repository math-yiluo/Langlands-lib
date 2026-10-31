# Actual rank-one convergence from matrix analytic data

Worker 396. Internal derived prerequisite for the actual matrix functional-equation
comparison. The field and representation-carrier universes are independent.

`ModelBoxConditions` records exactly the positive principal level, nonnegative
support cutoff, nonpositive character-trivial lattice level, first-row lattice
estimate, character triviality, level-set inclusion, right stabilizer and rank-one
support bound needed by the published box integral calculation.

`exists_box_averagedModelCoefficient_eq` supplies these conditions for every
actual model vector of a smooth representation of `GL_(m+2)`. It chooses the
principal level inside the right stabilizer, its preimage under the continuous
determinant-rank-one endomorphism, and the required first-row neighborhood.
The support cutoff is enlarged to be nonnegative, and the character lattice
level is the minimum of its actual additive conductor and zero. An elementary
transvection gives the level-set inclusion.

It then chooses a compact open subgroup inside both a left stabilizer of the
actual box indicator and the same determinant-rank-one preimage. The conclusion
retains compactness, left test invariance, determinant norm one and pointwise
equality of its actual normalized averaged coefficient with the model function
throughout the box. Test invariance keeps each left translate in the box. The
pointwise box identity reduces both values to determinant diagonals, which
commute. Right stabilization removes the averaging element's determinant
image, so the normalized average integrates a constant at each box point.

`box_comparison_of_integrable` reverses the published box calculation. For any
parameters satisfying `ModelBoxConditions`, one real constant `C > 0`, independent
of the complex spectral parameter, gives both absolute rank-one convergence
from absolute matrix convergence and

```text
Z(boxIndicator, s + (m+1)/2, W) = C * Psi(s, W).
```

The constant is the restricted integral-group mass of the box support times the
tail-torus mass times the unipotent-box mass. All three masses are finite and
strictly positive. The implemented norm argument first uses the published
Iwasawa support reparametrization and product Tonelli identities. The `GL1`
measure density converts the shifted matrix exponent into the actual rank-one
exponent `s-(m+1)/2`. If the rank-one norm integral were infinite, its product
with the positive masses would be infinite, contradicting matrix integrability.
Continuity supplies strong measurability. The Bochner versions of the same
identities then give the exact integral factor.

`box_matrixIntegrand_eq_of_eq_on_box` extends equality on the box to equality
of the entire cutoff-weighted matrix integrands, since both vanish off the box.
`rankOneModel_convergesOnRight_of_matrix` applies this equality to the actual
averaged coefficient. A common right half-plane from the supplied matrix
coefficient model therefore works for every original rank-one model vector.
The box and compact subgroup may depend on that vector, but the half-plane
bound is unchanged.

`rankOneModel_rationalContinuation_of_matrix` also uses the supplied rational
continuation of the actual averaged coefficient's box integral. Multiplication
by `C^{-1}` and equality on a right half-plane give a rational continuation
for the specified original rank-one model integral, together with its absolute
convergence. No normalized-generator identification is needed in this deduction.

These results derive from published model smoothness and support, compact open
subgroup existence, the box decomposition and exact integral identities, and the
pointwise BoxCoefficient helper. They assert no new transcription from the
literature. The analytic hypotheses are the actual matrix assertions of the
specified coefficient model; no irreducibility, finite length or extra Whittaker
convergence premise is used. Inverse-transpose convergence, the paired Fourier
extraction and the final gamma functional equation remain later obligations.
