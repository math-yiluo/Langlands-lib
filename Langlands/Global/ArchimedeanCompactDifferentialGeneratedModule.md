# The actual compact-and-differential generated module

This internal construction realizes the explicit complex span of compact
translates of genuine enveloping derivatives as an actual enveloping submodule.
The vector and every natural rank are arbitrary; compact finiteness is not
needed for these identifications.

The full complex enveloping action span of a complex subspace equals the
restriction of scalars of its enveloping span. Closure of the full action span
under further enveloping action follows by multiplying the acting coefficients.
Span induction proves the equality.

`compactDifferentialGeneratedModule` is the genuine enveloping span of the
entire actual compact orbit span. `compactDifferentialGeneratedSpan` is exactly
the explicit complex span in the published compact-type central-span statement.
Actual covariance identifies them after restricting scalars: a differential of
a compact translate is a compact translate with inversely conjugated
coefficient, and the converse uses direct conjugation.

The entire compact group preserves the generated module. On source orbit
vectors this is compact orbit stability; on their enveloping actions this is
actual covariance. Thus the module carries its restricted actual compact
representation, whose compatibility with the genuine enveloping action is
proved by faithful inclusion into the derivative smooth carrier.

These definitions and equalities retain the original actual compact group,
genuine differential operators and all number-field universes. They do not yet
lift the finite compact source into this module, prove the comparison of an
ambient isotypic intersection with its restricted-module isotypic span, or prove
the compact-type covering or automorphic growth statements.
