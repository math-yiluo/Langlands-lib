# Conditional assembly for derived split-torus centralizers

Author: Worker 1366.

This module assembles the exact public statement
`SplitTorusCentralizerDerivedSimplyConnectedStatement.{u}` from six explicit
structural hypotheses. It is a conditional theorem, not an unconditional
proof of the target. The universe `u` is arbitrary throughout.

`SplitTorusCentralizerDerivedInputsStatement.{u}` defines the conjunction of
the six structural statements used below. It asserts that all six hold and
adds no replacement assumption on individual groups or lattices.

`splitTorusCentralizerDerivedSimplyConnectedAlgClosed_of_inputs` proves the
algebraically closed case assuming:

- `DynamicCentralizerReductiveStatement.{u}`;
- `DerivedSubgroupSemisimpleStatement.{u}`;
- `SplitSimplyConnectedCorootSpanStatement.{u}`;
- `SplitCorootSpanSimplyConnectedStatement.{u}`;
- `SplitTorusCentralizerDerivedCorootComparisonStatement.{u}`.

For the given split subtorus, the proof chooses the existing centralizing
cocharacter, whose dynamic centralizer is the supplied whole-torus
centralizer. Its representative is closed by the proved geometric-reduction
helper. Dynamic-centralizer reductivity then applies to that very
representative. The derived-semisimplicity hypothesis supplies semisimplicity
of the actual derived group.

The geometric comparison hypothesis supplies actual compatible split maximal
tori, reduced root data `P` for the ambient group and `Q` for the derived
group, and a closed torus map whose cocharacter map carries `Q.corootSpan ℤ`
onto the span of a subset of the simple coroots of a base of `P`. The coroot
necessity hypothesis makes `P.corootSpan ℤ` the whole ambient cocharacter
lattice. Semisimplicity of the derived group gives a finite quotient by
`Q.rootSpan ℤ` using the proved `IsSemisimple.finite_quotient_rootSpan`; the
proved root/coroot finite-index equivalence makes the quotient by
`Q.corootSpan ℤ` finite. Closedness of the actual torus map gives injectivity
on cocharacters. The proved integral saturation argument in
`LeviCorootLattice` now makes `Q.corootSpan ℤ` the whole derived cocharacter
lattice. The sufficiency hypothesis yields simple connectedness of the
derived group.

`splitTorusCentralizerDerivedSimplyConnected_of_inputs` adds the sixth
hypothesis, `IsSimplyConnectedAlgebraicClosureAscentStatement.{u}`. It invokes
the proved algebraic-closure reduction from the companion
`SplitTorusCentralizerDerivedGeometricReduction` module. That reduction
transports every supplied inclusion and its all-test property to the
algebraic closure and reflects the final conclusion to the original field.
`splitTorusCentralizerDerivedSimplyConnected_of_input_bundle` supplies these
six hypotheses from their defined conjunction.

The provenance is the combination of the already proved integral saturation,
base-change and reflection lemmas with the displayed structural statements.
Every remaining structural assumption is a named proposition, rather than a
hidden replacement for the target. The geometric comparison retains more
actual-object data than this assembly consumes; in particular the compatible
ambient square and reducedness of `Q` are part of that statement but are not
needed in the final lattice argument.
