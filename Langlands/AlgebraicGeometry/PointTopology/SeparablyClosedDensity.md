# Conditional rational density of smooth schemes

This internal adapter derives density of actual rational sections of a smooth
scheme over a separably closed field from the exact published algebraic
proposition `Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement`.
That proposition remains an explicit argument; this module does not prove it.

`isGeometricallyReduced_of_smooth` applies the algebraic criterion for geometric
reducedness over a field: reducedness after tensoring with its algebraic closure.
Smoothness survives this scalar extension. The published smooth-algebra
reducedness lemma then applies over the algebraic closure, which is a domain.
This helper permits independently sized field and algebra universes.

`nonempty_rationalPoint_of_smooth_spec` expresses a given affine structure
morphism as the spectrum of a ring homomorphism and equips its coordinate ring
with the corresponding algebra structure. Scheme smoothness gives algebra
smoothness, hence finite type and geometric reducedness. Nontriviality of the
coordinate ring and the supplied algebraic proposition produce an algebra map
back to the ground field. Its spectrum is a section of the original structure
morphism, because the algebra map respects scalars.
`rationalPointOfSmoothSpec` chooses such an actual rational section using
classical choice.

`hasDenseRationalPoints_of_smooth_of_rationalPointStatement` tests density
against every nonempty open subset. An affine open neighborhood inside that
subset is nonempty and smooth over the ground field. The preceding affine
construction gives a rational section there. Composing its inclusion into the
original scheme exhibits a point of the open subset in the image of an actual
rational section. This includes empty schemes automatically and requires no
global affineness, connectedness, separatedness or quasi-compactness assumption.
The field and scheme have the same arbitrary universe, as in the published
rational-point and density interfaces.

The provenance is internal: these are deductions from the cited published Lean
interfaces and Mathlib's spectrum equivalence, smooth base change and affine
neighborhood construction. No source theorem, density assertion or structural
unipotent classification is silently assumed. In particular, the adapter does
not discharge the algebraic rational-point theorem or the all-field unipotent
woundness criterion.
