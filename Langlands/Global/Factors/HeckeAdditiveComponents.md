# Additive restrictions and finite integral support

Worker 1692, supporting constructions for the actual global Hecke functional
 equation. These are internal derived constructions on the existing actual
adele ring and its published topology.

The finite and infinite additive inclusions set every other coordinate to zero.
The finite inclusion is continuous by factoring through the restricted product
for the principal filter on the complement of the chosen singleton, then using
the continuous inclusion into the cofinite restricted product. The infinite
inclusion is continuous by continuity of the single-coordinate product map.
The product of all completed integer rings is included through the existing
restricted-product structure map, with infinite coordinate zero.

A continuous additive character on any product of additive groups has trivial
single factors outside a finite set. The proof pulls back the complex ball of
radius one half about one, extracts a basic product neighborhood, and applies
the published small-powers complex-number lemma to all nonnegative multiples
of a single-coordinate element. Applying this to the integral product proves
that every continuous unitary character of the adeles is trivial on local
integers outside a finite set. This conclusion does not require triviality on
the diagonal field.

The finite restriction is first constructed as a continuous `AddChar`. Under
an explicit hypothesis that this restriction is nontrivial, it gives exactly
`IsFiniteAdditiveComponent` and a `Nonempty SelfDualHaar` witness from the
published theorem `HarmonicAnalysis.padicSelfDualMeasureExists`. The finite
completion and its `CompletionPadic.topologicalData` have the same topology
by construction.

This module does not prove that diagonal-trivial global characters have
nontrivial restrictions at every place. It also does not assert conductor
zero outside a finite set: integral triviality gives only the corresponding
one-sided conductor bound. Those arithmetic inputs and the global functional
 equation remain separate obligations. The source motivation is Tate,
*Number theoretic background* (1979), sections 3.5–3.6, printed pp.15–17,
registered as `tate-1979-number-theoretic-background`.
