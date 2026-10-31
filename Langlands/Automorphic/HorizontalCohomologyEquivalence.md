# Full operator equivalences on actual horizontal cohomology

Let `F : Type u` be a number field and let `n : ℕ` be positive, expressed by
`NeZero n`. For actual complex operator realizations
`S T : OperatorRealization F n`, a full operator equivalence
`e : S.Equivalence T` induces two complex-linear representation equivalences
for every natural degree `q`, including zero:

- `Equivalence.horizontalCyclesEquiv e q` goes from
  `S.horizontalCyclesFiniteRepresentation q` to
  `T.horizontalCyclesFiniteRepresentation q`.
- `Equivalence.horizontalCohomologyEquiv e q` goes from
  `S.horizontalCohomologyFiniteRepresentation q` to
  `T.horizontalCohomologyFiniteRepresentation q`.

These are the existing finite adelic representations on actual horizontal
cycles and cohomology. The cycle module is the kernel of the actual reduced
horizontal differential. Cohomology is its quotient by actual image
boundaries. Horizontality in every Lie-algebra argument and equivariance for
the full standard infinite compact group remain the defining cochain
conditions; no connected-group replacement is made.

Both constructors specialize the published generic
`Horizontal.equivCycles` and `Horizontal.equivCohomology` to the actual
compact image, reduced compact action and coefficient action. Their cochain
equivalence is the existing `e.horizontalEquiv`, which postcomposes
coefficients by `e`. A private chain lemma reverses the already proved
`horizontalEquiv_differential` equation and unfolds the actual and generic
differential wrappers. Thus differential compatibility is proved from the
full operator equivalence, rather than supplied as another input.

The generic cycle construction restricts the cochain equivalence and uses
the inverse cochain equivalence for its inverse. The generic cohomology
construction descends those chain maps to the actual quotient. The generic
proof derives inverse differential compatibility from the forward equation
and proves both inverse laws on cycle representatives. Finite adelic
equivariance is retained in both directions. Ten explicitly named local
additive-group instances are exactly the canonical `Submodule.addCommGroup`
structures on the five successive function spaces, `S.Space`, `T.Space`,
the exact generic source and target cochain spaces, and the generic cycle
space parametrized by an operator realization and degree.
They supply no additional hypothesis or operation.

The provenance is internal specialization of published
`HorizontalEquivalence`, `HorizontalCohomologyFinite` and generic
`HorizontalCohomologyEquivalence`. No external-literature comparison is
asserted. This pair constructs only the two equivalences; separate API laws
can identify their underlying intertwiners and representatives. It supplies
no topology, smoothness, nonvanishing, irreducibility or automorphic spectral
existence assertion, and does not complete the broad global infrastructure.
