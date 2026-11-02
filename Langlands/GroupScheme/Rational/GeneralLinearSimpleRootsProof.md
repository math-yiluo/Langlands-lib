# Simple relative roots of the diagonal torus

Worker 163.

This derived helper for `GeneralLinearStandardParabolicStatement` identifies the
simple relative roots of the actual diagonal torus of `GL_N` over any field.
Its hypothesis is that the integer coordinates of the chosen cocharacter are
strictly decreasing. The proof works uniformly for every natural number `N`,
including zero and one, and uses the existing character lattice and Lie roots.

The published root computation and root-datum comparison express every root as
the character with integer coordinate vector `e_a-e_b`, where `a ≠ b`.
The lattice pairing is the difference of the corresponding cocharacter weights.
Strict decrease therefore makes this root positive exactly when `a < b`.

For indecomposability, pair characters with the auxiliary cocharacter whose
weights are the negatives of the coordinate indices. Every positive root has
integer height `b-a ≥ 1`. Adjacent characters have height one, so additivity of
the lattice pairing rules out a decomposition into two positive roots. Conversely,
a positive root with nonadjacent indices is the sum of the positive roots with
indices `(a,a+1)` and `(a+1,b)`. The coordinate equivalence proves that equality
of actual characters. Thus indecomposable positive roots are exactly the adjacent
characters already defined in `GeneralLinearIndexing`.

The root positivity and integer-height arguments are derived finite-coordinate
formulations. The conventions come from Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Example 2.1.1, printed pp.45–47,
(source `conrad-gabber-prasad-2015-pseudo-reductive`, PDF pp.71–73),
and Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, V.3.8, printed p.111
(source `renard-2026-representations-groupes-reductifs-padiques`, PDF p.117).
Renard works over a nonarchimedean local
field; the arbitrary-field scope here follows from the published algebraic
matrix and character-lattice constructions. This helper proves the simple-root
computation; subgroup intersections and rational-point identifications are the
other parts of the full target.
