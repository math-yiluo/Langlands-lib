# Smooth complex characters on the actual rational norm kernel

Author: Worker 200.

This is an internal, derived adapter for the real-descent route already
implemented in `RationalSmoothRealDescentConstruction`. It does not add an
external structural assertion or prove any of that route's three actual
local-point prerequisites.

For an arbitrary group `G`, a complex character `theta : G →* ℂˣ` and a real
base `q`, `complexCharacterLogModulus q theta` is a homomorphism from `G` to
`Multiplicative ℝ`. Its value, read additively, is

`-Real.log ‖(theta g : ℂ)‖ / Real.log q`.

The construction applies `Units.map` to the actual nonnegative norm
homomorphism and then uses the published `normLog`. Thus it uses the same
negative-exponent convention as the valuation-image real part. The real
target is tagged multiplicatively only to accept a homomorphism from `G`.
No continuity of the logarithm is needed.

For `1 < q`, `complexCharacterLogModulus_eq_one_iff` identifies membership
in this homomorphism's kernel with `‖(theta g : ℂ)‖ = 1`. The proof applies
`normLog_eq_zero_iff` to the positive unit and compares its underlying real
value. `ker_le_complexCharacterLogModulus_ker` also holds for arbitrary
`q`: a point at which the character is one has logarithmic modulus zero.
Consequently `isOpen_ker_complexCharacterLogModulus` proves that an
open-kernel complex character has open-kernel logarithmic modulus. This
step requires only separately continuous multiplication on the domain,
because a subgroup containing an open subgroup is open.

The actual-group theorem
`norm_eq_one_on_rationalCommonNormKernel_of_structure` takes:

- an arbitrary nonarchimedean local field `F`, in equal or mixed
  characteristic;
- a connected reductive group scheme `M` over `F`;
- `CentralNormKernelCompactness M hM`;
- `CentralDerivedNormKernelCocompactness M hM`;
- `DerivedSmoothRealAnnihilation M hM`.

Its conclusion is that every complex character of the actual rational
points with open kernel has norm one on
`rationalCommonNormKernel M`. The topology is exactly
`rationalPointTopology F M.X`; affineness and smoothness come from
`hM`. Field and generic-group universes are independent. No split or
quasisplit hypothesis is added.

The implemented proof uses `LocalField.residueCardinality F` as its
logarithm base and the proved inequality that it exceeds one. The new
open-kernel lemma lets the published
`rationalCommonNormKernel_le_ker_of_structure` apply to this real
homomorphism. The kernel/norm equivalence then gives the conclusion.

The three named premises are actual local-point targets, not proofs
supplied by this adapter and not newly permitted external inputs for the
Plancherel program. In particular, derived rational points are not
identified with abstract commutators. This module does not establish
unconditional smooth real descent, norm-kernel unitarity for every
reductive group, finite index of a split-component image, or unitary
detection from a split component. It supplies the exact norm-kernel
premise for the latter's finite-quotient argument.
