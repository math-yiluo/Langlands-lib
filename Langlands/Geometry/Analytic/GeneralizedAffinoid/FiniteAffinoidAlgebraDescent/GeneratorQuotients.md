# The global generator quotient and its original local comparisons

For every finite matching tuple, this construction forms the presented
quotient by the closed kernel of the global evaluation. That evaluation
descends to a bounded injective map from the quotient to the matching
algebra. Injectivity follows from the exact kernel equality.

The local admissibility, kernel identification, and comparisons assume
that the same tuple projects to module generators of each original local
algebra over its original cover algebra. In Lean, each projected tuple
has a surjective coefficient map. This hypothesis and the supplied
finite Banach structures give admissibility of each local evaluation.

`restrictedEvaluation_isAdmissibleEpi` obtains further evaluation
admissibility by arbitrary bounded base change of an admissible local
evaluation, followed by the constructed bounded pushout equivalence.
The equivalence is admissible by its bounded section.

Fix an original cover member and a full domain `E` whose locus is
contained in that member. `restrictedEvaluation_kernel_global`
identifies the kernel of the evaluation for this restriction with the
closed extension of the global kernel. It combines the further-kernel
theorem, ideal effectiveness, composition of closed extension, and the
weighted restriction's coefficient triangle. `domainQuotientEquiv`
uses `ClosedQuotient.baseChangeEquivOfAdmissibleEpi` to identify the
quotient pullback with the original base change of the chosen local
algebra to `E`. `localQuotientComparison` uses the same result on each
original weighted cover member to identify its quotient pullback with
the entire original local algebra. Both comparisons retain the entire
original coefficient leg.

These are derived from the explicit bounded evaluation, effective ideal,
full-domain base-change and admissible quotient APIs. The construction
retains arbitrary positive polyradii, trivial valuations and empty spectra.
