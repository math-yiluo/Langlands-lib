# Actual normalized framing and its formal chart-transition equation

This internal module defines `chartFraming` of an actual
height-zero framed atlas on a defined original chart of its
reduced target. Its source is the fixed frame extended along the
stored residue map and then directly to the test algebra. Its
target is the tested reduced-target chart. It composes the inverse
actual global-chart isomorphism with the original actual
full-order quasi-isogeny on that chart.

All local-field, central-division-algebra, embedded-subfield,
residue-field, height-certified fixed-frame and fixed-`Nilp`
hypotheses and universe restrictions of the framed representative
remain. The target's principal cover may be infinite.

`refinedChartFraming_eq_chartFraming` identifies the previously
defined arbitrary-refinement framing with this chart normalization
followed by the inverse actual refined-chart identification. Its
proof is definitional equality.

`chartFraming_transition` applies the actual reduced-target
transition from a defined chart `b` to another defined chart `c`.
The result is precisely `chartFraming` on `c`, as equality of
entire actual full-order quasi-isogenies.

The proof starts with the original framing's rational transition
square. It precomposes by the inverse global-chart identification
at `b`, uses associativity, and then uses
`globalOrderChartQuasi_transition` to identify the source route
with the inverse global-chart identification at `c`. Thus it
compares actual rational maps, without any inference from their
values on points.

The provenance is internal from the original actual framing,
the constructed full-order chart transitions and the proved
global-frame transition coherence. The definition still retains
the original representative's height-zero certificate; this file
does not separately prove a height statement for `chartFraming`.
Arbitrary refinement/source-choice comparison coherence, collapse
of comparison chains, varying-base functoriality and
representability remain separate.
