# Actual test-chart comparison through coefficient extension

This module proves coefficient extension of a specified actual refined
full-order comparison preserves its actual isomorphism between fixed test
charts. Both sides retain their actual integral inverse formal maps.

The proof uses full formal-coordinate extensionality. The complete series of
the test comparison exposes its two outer transitions. The refinement
coefficient corrections are the actual original parent transitions, and the
extended comparison map retains the complete original comparison series.
The two original transition cocycles combine the outer corrections. The proved
source-chart equality for equal image covers aligns the retained original
finer source chart. No detection by point evaluations is used.

Coefficient and acting rings may have separate universes; source and target
coordinate types are arbitrary finite types. Covers may be infinite, and
coefficient maps may merge generators. Every supplied finer or outer test
chart has its actual unit evidence. `baseChangeOriginalTestIso` constructs transport from any specified original
finer chart on the restricted test through the two actual coefficient-chart
isomorphisms. `testIso_baseChange_eq_original` combines the proved square
with whole original test-comparison independence to identify this isomorphism
with the specified extended test comparison. Both finer charts are supplied
with unit evidence, and the theorem permits different choices.

Independently supplied target scalars,
quotient naturality and original framed comparison base change are outside
this module; `DrinfeldFramedComparisonBaseChange` constructs
`DrinfeldFramedAtlas.Comparison.baseChange`.
