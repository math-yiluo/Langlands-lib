# Bounded Hecke operators on full closed Hilbert-slice fixed spaces

Author: Worker 2.

This internal construction equips the existing algebraic compact-open Hecke
corner action with bounded endomorphisms for the inherited ambient norm. The
actual application is to all subgroup-fixed vectors of the actual closed tensor
slice in a supplied global positive-form Hilbert completion.

`TensorHilbertHeckeAux.cornerSampleBound` is the finite sum of the norms of the
existing `fixedLevelActionSamples` coefficients for the same Haar measure,
compact open subgroup and corner element. It is nonnegative and independent
of the representation, invariant subspace and vector. It is a bound; no
identification with the Haar L1 norm is asserted.

For an ambient complex normed representation whose original group operators
preserve the norm, `cornerAction_norm_le` bounds the existing full-fixed-space
action by this constant times the inherited vector norm. The proof uses the
existing finite formula in the unchanged ambient group operators, the triangle
inequality for the finite sum, norm multiplicativity under complex scalar
multiplication, and the explicit group-operator norm identity.

`cornerContinuousAction` uses `LinearMap.mkContinuous` to package each unchanged
operator as a continuous complex-linear map. Extensionality and the existing
algebra homomorphism laws prove that these bounded operators form a unital
complex algebra homomorphism. `cornerContinuousAction_toLinearMap` recovers the
exact previous algebraic operator by reflexivity. The operator norm is at most
`cornerSampleBound`, by Mathlib's norm estimate for this same constructor.
The ambient group and normed carrier have independent universes. Neither
completeness nor smoothness of the entire ambient representation is required.

`FiniteTensorPresentation.sliceHilbertContinuousCornerAction` specializes to
the actual full `sliceHilbertRange` fixed space. The ambient space is the
original `b.HilbertCompletion`; its action is the original completed global
representation restricted along actual finite-local GL_n insertion. The
published `completedRepresentation_norm` supplies norm preservation directly,
without a new analytic premise. The field and original factor carriers have
independent universes, coefficients are complex, and every natural rank is
included. A genuine tensor presentation, global invariant positive form, tail,
Borel Haar measure and compact open subgroup are explicit. Zero tails are
included, and no admissibility, irreducibility or nonzero-tail input is needed.

The provenance is an internal derivation from the existing ambient finite-sum
formula, norm-preserving completed group action, and Mathlib's bounded linear
map constructor. There is no new original-literature identification. The unit
constructs bounded operators on the full fixed space only; it asserts no
Bochner integral on the full Hilbert space, Haar L1 estimate, continuity as a
map from a topology on the Hecke algebra, existence of the supplied form or
presentation, spectral occurrence, decomposition, or canonical normalization.
