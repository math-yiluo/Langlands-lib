# Haar-choice invariance of analytic temperedness

`Langlands.glTemperedHaar` proves exactly the published closed proposition
`Langlands.GLTemperedHaarStatement.{uF, uV}` and exposes its two
components as `glTemperedFixedHaar` and `glLeviTemperedHaarExtension`. It also
provides the convenience theorems
`PadicField.TopologicalData.isTempered_iff_fixedHaar` and
`RelativeRegularComparison.isLeviTempered_iff_fixedHaar`.

For two Borel measurable-space realizations of one fixed topological quotient,
`BorelSpace.measurable_eq` identifies both measurable spaces with its Borel
sigma algebra. After substituting this equality, the proof preserves the
admissibility proof and the same unitary central-character witness. For each
smooth-dual functional, vector, and positive real `ε`, it applies
`Langlands.haarMemLpInvariant` at exponent `ENNReal.ofReal (2 + ε)` to the same
descended absolute coefficient. The private helper contains this argument
without changing the representation or the topology. The source and target
measurable-space, Borel-space, measure, and Haar-instance binders remain explicit
in the actual-Levi extension and in the use of that extension by the convenience
equivalence. The helper alone disables the overlapping-instances linter because
these two Borel realizations are its intended inputs; this changes no proof
checking or theorem hypotheses.

`Langlands.glBlockCentralQuotientTopology` supplies the topological-group,
locally compact, and second-countable instances on the actual GL and
product-Levi quotients by their full group centers. For the ambient GL
criterion, the source Borel realization is first identified with the canonical
one used by `T.IsTempered`; then the same coefficient argument handles every
Haar normalization. The forward implication specializes the universal
predicate. The product-Levi convenience equivalence specializes the universal
predicate in one direction and uses the extension theorem in the other.

These arguments have no irreducibility or invariant-form premise. They retain
the supplied `T`, arbitrary Borel realizations, all ranks, and independent
field and carrier universes. This is an internal derivation from the cited
Library theorems, not a new translation of a literature assertion. It supplies
measure-choice adapters only; the analytic construction of an invariant
positive form remains a separate obligation.

The proof is reused from Worker 560's parent-task draft revision 2, with Worker
551's precise cross-Borel Levi interface. Worker 403 integrated the proof pair
against the published statement and supplied this final proof documentation.
