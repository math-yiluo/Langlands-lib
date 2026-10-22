# Common characters, test functions and additive Fourier transform

This module implements the common harmonic-analysis types for the arithmetic
and representation-side local-factor branches. The namespace is
`Langlands.HarmonicAnalysis`.

`UnitaryAdditiveCharacter F` consists of a continuous nontrivial
`AddChar F Circle`. Its complex-valued realization is the composite with
the unit-circle inclusion, whose continuity and modulus-one property are
proved. No additive character is chosen from an assumed existence theorem.
`Quasicharacter F` abbreviates Mathlib's `ContinuousMonoidHom Fˣ ℂˣ`;
it adds no unitarity constraint to a multiplicative quasicharacter and
creates no duplicate character structure.

`schwartzBruhatSubmodule X` is the actual complex submodule of `X → ℂ`
consisting of locally constant functions with compact support.
`SchwartzBruhat X` is its carrier, with inherited vector-space structure
and coercion to functions. Closure under addition and scalar multiplication
is proved. This is the nonarchimedean test space; it is not the archimedean
rapidly decreasing Schwartz space.

`AdditiveHaarMeasure F` bundles a measure with the existing Mathlib additive
Haar and regularity predicates. `normalizedAdditiveHaar K` constructs one
using Mathlib's proved Haar measure construction, normalized on a supplied
compact set with nonempty interior. This normalization is not claimed to
be Fourier self-dual.

`fourierIntegral` uses the kernel `ψ(x*y)` with a plus sign.
`fourierTransform` is a complex linear map from `SchwartzBruhat F` to
`F → ℂ`. Its integrand is proved integrable using continuity, compact
support, and finiteness of Haar measure on compact sets. The unrestricted
raw Bochner integral has Mathlib's usual convention on nonintegrable
functions; the test-function transform does not depend on that convention.
The output has not yet been bundled as a test function: Fourier
preservation of this space requires a separate theorem.

`IsSelfDual ψ μ` states that the iterated Fourier integral converges on
every test function and equals reflection `f(-x)`.
It is formulated here for locally compact, Hausdorff, totally disconnected
topological fields, where these are the intended nonarchimedean test functions.
`SelfDualMeasureExists ψ` is the associated existence proposition.
Neither is an assumption of another construction, and no global self-dual
measure is chosen here. These definitions are to be specialized to the
published finite-p-adic-field topological realization.

## Original sources and status

Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions L*
(1973), sections 3.1–3.3, internal/PDF page 26 (printed page 526):
continuous quasicharacters, Haar measures, compactly supported smooth
functions, and the plus-sign Fourier integral. In the nonarchimedean case
smooth functions mean locally constant functions.
Registered source `deligne-1973-local-constants`, retained PDF
`C:/Central-Library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`,
SHA256 `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
Internal pages 23–33 were read, and page 26 was inspected visually.

John Tate, *Number theoretic background* (1979), section 3.2, page 13,
and section 3.6, page 17, supply the Fourier and self-dual conventions.
Registered source `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
retained in the Corvallis Part II volume. Printed page `p` is PDF page `p+9`;
pages 10–21 were read. The intrinsic self-duality predicate deliberately
does not use Tate's disputed scalar-measure ratio.

The submodule packaging and intrinsic Fourier predicate are derived Lean
implementations of these objects, not transcriptions of an existence proof.
There are no project mathematical dependencies. The pinned environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 20 authored this construction. Native compilation completed without
diagnostics. Development checks are separate from independent semantic
review and publication; this file makes no acceptance claim.
