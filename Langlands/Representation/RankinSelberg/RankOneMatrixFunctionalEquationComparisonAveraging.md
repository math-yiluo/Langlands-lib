# Paired compact averaging for matrix functional equations

This module constructs an actual normalized bi-smooth coefficient of the
specified Whittaker model and compares both its original and inverse-transpose
matrix integrals. Field and representation-carrier universes are independent.

## Provenance and scope

This is internal derived content following the compact averaging computation
of Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms on GL(3)* (1979),
printed pages 186–187, equations (3.1.3)–(3.1.4). It reuses Worker 249's generic
Fubini lemma and compact-integration smooth functional from `LeftAveraging`
and `WhittakerAveraging`. The latter module's local instances have explicit
names so it can be imported together with `GodementJacquet.AnalyticData`.

The representation is assumed smooth. No irreducibility, admissibility,
finite generation, nonzero functional, self-duality, Fourier-pair existence,
or exponent-zero normalization is used. The character has the published
`UnitaryAdditiveCharacter` type, including its continuity and nontriviality.
Every integral-preservation assertion assumes convergence of the relevant
original integrand. In particular, this module does not deduce Whittaker
convergence from averaged matrix convergence or complete the positive-rank
functional-equation comparison.

## Generic normalized average

`normalizedLeftAverage μ Ω W` is the function

`g ↦ (μ.real Ω)⁻¹ ∫_{x ∈ Ω} W(x g) dμ(x)`.

The definition is total, including at zero or infinite mass. The theorem
`normalizedLeftAverage_integral` assumes a measurable finite-mass set of
positive mass, an s-finite left-invariant group measure, measurable group
operations, left invariance of the weight `a` under `Ω`, and integrability
of `g ↦ a(g) W(g)`. It proves integrability of the averaged weighted function
and equality of its integral with the original. The proof applies
`leftAverage_integral`, multiplies by the reciprocal mass and cancels that
finite nonzero mass. It does not reverse an averaging convergence implication.

`normalizedLeftAverage_comp` uses a measure-preserving group automorphism
`e` that is a measurable embedding. It proves

`normalizedLeftAverage μ Ω W (e g) = normalizedLeftAverage μ (e⁻¹ Ω) (W ∘ e) g`.

The change of variables on the restricted measure proves the set-integral
identity, and measure preservation identifies the two normalizing masses.
Neither convergence nor a nonzero-mass hypothesis is needed for this identity
of totalized integrals.

## Actual model coefficient and paired integrals

`Padic.averagedModelCoefficient` takes a smooth representation `σ`, its
specified functional `ℓ`, a compact open subgroup `K` and an element `w` of
the actual coefficient model. It is the scalar `(μ.real K)⁻¹` times the
bi-smooth coefficient of `w` against `modelSetIntegralDual`, with
`μ = generalLinearHaar F.Carrier n`. Its membership in the bi-smooth
coefficient submodule follows from the generating span, and
`averagedModelCoefficient_apply` identifies its value with the normalized
left average of `glModelFunction ψ n σ ℓ w`.

`matrixIntegral_normalizedLeftAverage` specializes the generic weighted
identity to `a(g) = Φ(g) |det g|^s`. Its hypotheses say that `K` fixes the full
matrix test `Φ` on the left and that every member has determinant norm one.
Compactness and openness supply finite positive Haar mass. The determinant
weight is therefore invariant under `K`, and the theorem proves both actual
`MatrixConverges` and equality of actual `matrixIntegral` values at every
parameter where the original integral converges.

`inverseTransposeOpenSubgroup` is the preimage of `K` under the actual
continuous inverse-transpose automorphism. Its compactness follows from the
homeomorphism. `coefficientIota_averagedModelCoefficient` applies the generic
change of variables and the published `generalLinearHaarSymmetries`: the
inverse-transpose transform of this very same coefficient is the normalized
average of `coefficientIota W` over that preimage subgroup, with the exact
same normalizing volume.

`averagedModelCoefficient_paired_integrals` combines the two applications.
It assumes left invariance and determinant norm one for `Φ` under `K` and
for `ΦHat` under the transported subgroup, and convergence of `W` and
`coefficientIota W` at arbitrary respective parameters `s` and `t`. The one
constructed coefficient preserves both convergence assertions and both
integral values. Here `ΦHat` is an arbitrary second test; a Fourier-pair
hypothesis is not part of this focused theorem.
