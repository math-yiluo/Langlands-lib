# Discrete-series actions separate the actual cuspidal Schwartz space

`RationalCuspidalDiscreteActionSeparationAtUniverseStatement` is a conditional
form of the last step of Waldspurger's proof of VIII.1.1. It uses the
actual rational-point Harish-Chandra Schwartz space and its intrinsic
cuspidal subspace. For a cuspidal Schwartz function `φ`, the vanishing
input is `ω(ˇφ) = 0` for every discrete series class, on the actual
admissible smooth representative with tempered coefficients. The
operator uses the given ambient Haar measure and the actual weight
estimate for `Ξ` and `σ`. The other analytic inputs are the central
weight estimate and finite dimension of the projected cuspidal
bi-invariant levels for each continuous unitary split-central character.
The action is tested in the prescribed carrier universe `uV`, independent
of `u`. `RationalCuspidalDiscreteActionSeparationStatement` is the
specialization to the carrier universe `max u uV` used by the upper
inclusion.

`rationalCuspidalDiscreteActionSeparationAtUniverse` constructs a compatible
measure for the left quotient and uses the given Haar measure on the
split-central group quotient to form the discrete series classes. The
split component is closed and central. Published unimodularity and
quotient Haar results give the measure invariances used in the proof.
The upper inclusion of VIII.4.2, in
`rationalCuspidalDiscreteUpperEstimate`, places each central projection
of `φ` in the sum of the specified discrete-series coefficient spaces.
This uses the finite-level hypothesis in VIII.4.1. The actual rational
point group is separable, so `discreteSeriesCentralCoefficientSpace_eq_of_separable`
identifies this sum with the one indexed by carrier universe `uV`.

Square integrability gives every representative in that sum an invariant
positive form. By the pairing identity of VIII.5, the vanishing of
`ω(ˇφ)` puts each smooth coefficient in the integrable annihilator
of `φ` for the ambient pairing. The same holds on their algebraic
sum. The quotient integration formula gives zero quotient norm for the
continuous central projection, so that projection vanishes everywhere.
Finally, Fourier uniqueness for the actual split center implies `φ = 0`.

In the source proof, `φ` is the reconstruction residual. Applying this
step to that residual requires its cuspidality and the conversion from
its group-index Fourier components to zero discrete-series actions.
[Waldspurger (2003), VIII.5, printed p. 332](https://doi.org/10.1017/S1474748003000082)

`RationalCuspidalDiscreteActionSeparationOfWeightsStatement` and
`rationalCuspidalDiscreteActionSeparationOfWeights` require the same
central and ambient estimates and finite projected levels for a general
matrix height. The weight-based upper inclusion supplies the coefficient
span used in the same annihilator argument. The closed-height
implication is its specialization.
