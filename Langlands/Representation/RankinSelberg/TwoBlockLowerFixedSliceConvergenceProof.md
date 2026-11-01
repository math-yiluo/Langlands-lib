# Fixed-slice absolute convergence of the Section 4.7 lower integrand

`Langlands.RankinSelberg.twoBlockLowerFixedSliceConvergence` proves exactly
`TwoBlockLowerFixedSliceConvergenceStatement.{uF,uV,uW}`. It has no additional
parameters or premises. The field, test representation and dependent block
spaces retain their independent universes. The full published Whittaker-type
hypotheses are used, with every supplied functional, including zero, and every
actual coefficient-image vector.

The original analytic assertion is in Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions* (1983), Section 4.7, printed pp. 412–414,
especially the assertion after (4.7.2) and estimates (4.7.3)–(4.7.5), together
with the test Whittaker estimates of Section 2.5. The registered source is
`jpss-1983-rankin-selberg`. The implemented proof uses coarse geometric growth
and support bounds in place of finite quasicharacter expansions. It proves
absolute integrability on the entire standard quotient and then restricts to
each requested slice. The compatible-measure and transport conclusions are
derived measure-theoretic packaging of that analytic assertion.

## Measures and the actual function

`compatible_measure_data` supplies right invariance of exactly the prescribed
`unipotentHaar`, existence of a quotient measure compatible with it and
`generalLinearHaar`, and sigma-finiteness of every compatible measure. Regularity,
local compactness and second countability give the latter conclusion.
Sigma-finiteness passes through the lower-to-standard measurable equivalence.
The lower measure remains exactly
`Measure.map (lowerToStandard h F.Carrier).symm νN`; no scale is introduced.
All topology, valuation and Borel instances in the proof are the canonical ones
specified in the target.

For any later parameter `u`, section `f`, coefficient `Wtest` and row
Schwartz–Bruhat function `Φ`, the proof calls the actual descended
`TwoBlockLowerUnfolding.integrand`, with the supplied inverse functionals
transported by `twoBlockOppositeTwistFunctional` and the supplied Fourier measure
`ν.val`. Call this function `E`. The imported `integrand_measurable` theorem
uses local constancy of the section, coefficient and translated-row Fourier
factors, followed by descent to the actual lower quotient. Thus `E` is
measurable. Composition with the inverse canonical lower-to-standard
homeomorphism makes
`Estandard q = E ((lowerToStandard h F.Carrier).symm q)` measurable as well.

## One threshold and a summable norm bound

The positive two-block shape implies `m 1 < t`, so the proof takes
`j : Fin t` with `j.val = m 1`. This is only the cut between the rotated
blocks, with no additional rank hypothesis. Put `s = Iic j.castSucc`,
`size lam = sum_i |lam i|`, and
`degree lam = sum_{i in s} lam i - sum_{i outside s} lam i`.
Here `q > 1` denotes the residue cardinality.

`exists_summable_integrand_majorant` provides a threshold `C` after the
representation and functional data and before `u`, the compatible measure,
section, coefficient, row function and slice integer. Its proof combines the
following bounds, detailed in the paired helper modules.

At the inverse image of the standard class of `g`, the test coefficient is
evaluated at `g`, while the section and partial Fourier factors are evaluated
at `blockRotation⁻¹ * g`. Moving this inverse rotation through a torus
representative permutes its integer exponents and preserves `size`. The
rotated section bound retains the actual opposite twists and contributes
`Cs * Bs ^ size lam * q ^ (-u * degree lam)`, with `Bs ≥ 1` fixed before
`u` and `f`. The inverse block half modulus is absorbed into `Bs`.
The test coefficient contributes a fixed growth base `Bw ≥ 1`. The compact
partial Fourier estimate, using the supplied Haar measure, contributes the
base `q`. Hence `B = Bw * Bs * q` is fixed before all later inputs.

Smooth root support bounds adjacent exponent increases uniformly over the
integral compact factor. The nonzero Fourier factor bounds the two exponents
bordering the cut from opposite sides. Propagating these bounds confines
nonzero integrand values to `OppositeCone M s`. Consequently the actual norm
is bounded uniformly in the integral compact factor by
`K * B ^ size lam * q ^ (-u * degree lam)` on that cone and is zero outside
it. The nonnegative amplitude `K` and natural cutoff `M` may depend on later
inputs; the base `B` does not.

The exact Iwasawa density is

`density lam = (prod_i prod_{j>i} normalizedAbs (varpi^(lam i) / varpi^(lam j)))⁻¹`,

at the canonical unit uniformizer `varpi`. It is definitionally the
`diagonalDensity` used by the majorant theorem. Its fixed growth bound is
`D ^ size lam`, where `D = q ^ (2 * (t + 1) * (t + 1))`.
The threshold is chosen so that `u > C` gives `u ≥ 0` and
`D * B * q ^ (-u) < 1`. On the opposite cone, `size` is at most `degree`
plus a constant depending on `M` and the rank. The elementary integer
geometric-series and finite-product comparison therefore prove summability
over the entire integer lattice.

Thus, for every permitted later input, the imported theorem supplies a
nonnegative real majorant `A lam`, uniform over every integral compact factor,
with `Summable (fun lam => density lam * A lam)`. Neither the quotient
measure nor the slice enters this estimate or the choice of `C`.

## Absolute integrability and restricted transport

`QuotientTorusEnvelope.integrable_of_summable_torus_bound` applies the
published normalized quotient Iwasawa measure identity to the measurable
function `Estandard`. Every compatible `νN` is the countable sum, over
integer torus exponents, of the compact-Haar pushforwards weighted by the
exact density above. The compact measure is Haar restricted to the integral
subgroup and has mass one. The proof converts membership in that subgroup
to membership in `integralOpen`, as required by the concrete bound.

For each exponent the uniform bound gives integrability on this probability
space and bounds its norm integral by `A lam`. After weighting, summability
of `density lam * A lam` bounds the sum of norm integrals. The countable-sum
measure criterion gives genuine Bochner absolute integrability of
`Estandard` for the supplied `νN`. This step establishes outer convergence.

Restriction gives absolute integrability on every standard determinant slice.
`integrable_lowerMeasure_iff` then gives absolute integrability of `E` on the
corresponding lower slice. Finally `integral_lowerMeasure`, once for `E` and
once for `fun z => ‖E z‖`, supplies the two requested restricted integral
equalities. The slice correspondence and measurable-equivalence pushforward
identity preserve the exact measures.

No convergence premise, irreducibility, induced Whittaker-type assumption,
functional equation or multiplicativity enters this argument. The proof
leaves the published target and its import closure unchanged.
