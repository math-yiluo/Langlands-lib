# Assembly helpers for arbitrary-thickening schemeness

Worker 336 implements the parent assembly. Worker 133 contributed the interface
and parent decomposition. The two input interfaces are abbreviations of the published `OpenFamilyLiftingStatement`
and `FiniteSurjectiveAffineDescentStatement`. The theorem
`schemeness_of_inputs` takes proofs of both exact propositions as explicit
hypotheses. The corollary `schemeness_of_finite_descent` uses the concrete
family-lifting proof and leaves finite-surjective affine descent as its sole
hypothesis. The entry module `SchemenessOfThickeningProof` applies this
corollary to the published theorem `finiteSurjectiveAffineDescent`, discharging
that hypothesis.

The helper `exists_affine_open_cover` chooses an actual scheme over the
original base representing the source, uses its native Mathlib affine open
cover, and transports the chart maps along the representing isomorphism.
The local `RespectsIso` instance explicitly unfolds the published
open-immersion predicate into its relative-property construction. The covering
sieve of the affine cover gives local surjectivity of the actual presheaf
coproduct for the slice fppf topology.

The lifting input supplies actual open algebraic spaces covering the target,
actual maps from the original affine charts, their unrestricted thickening
proofs and genuine pullback squares. `thickening_finite` applies the published
`IsThickening.finite`; each chart map is also geometrically surjective by the
published thickening definition. The descent input therefore supplies actual
affine scheme representations of the lifted spaces. The proof precomposes
the lifted open inclusions with those representing isomorphisms.
`coproduct_cover_of_isos` transports local coverage. The exact gluing theorem
`openChartGluing` then supplies an actual scheme over the original base and
an actual natural isomorphism representing the target.

This is internal connective content derived from the published geometric
predicates, the exact prerequisite statements and native Mathlib affine-cover,
relative-property and coproduct APIs. It introduces no geometric assumptions
or alternative definitions. All intermediate universe parameters and the
unrestricted thickening are retained. Its source route is the affine-open
lifting, affine descent and gluing decomposition described in the paired
prerequisite modules. The finite-descent theorem is imported and applied in
the entry module; the approximation and cohomological arguments remain in
that theorem's published dependencies. The assembly helpers are derived
connective content for the exact parent statement and do not modify its
published definitions.
