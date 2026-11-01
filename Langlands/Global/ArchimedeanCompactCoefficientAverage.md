# Matrix-coefficient averages for the actual compact action

Author: Worker 94.

This internal development applies the actual scalar weighted averaging operator
to the inverse matrix coefficients of a published `ContinuousCompactRep`.
For a fixed smooth input and a fixed coordinate of the source model, the
resulting map from the finite-dimensional source is complex linear.
Left invariance of the finite measure and the substitution `k = h l` show that
this map intertwines the source representation with the actual compact action
on derivative smooth functions. The proof uses scalar evaluation integrals;
it does not integrate in the smooth carrier.

The degree times inverse character is defined as the finite sum of the diagonal
matrix coefficients, multiplied by the dimension. Its average is correspondingly
a finite sum of values of these actual intertwining maps. Consequently every
value lies in the published algebraic isotypic span, without replacing that
span by its closure. Weighted averaging also gives continuity in the entire
derivative topology and containment in the closed compact-orbit span of the
input.

The finite diagonal sum is also identified with the matrix trace. Cyclic
invariance of trace makes its weight satisfy `w(h k) = w(k h)`.
For a finite measure invariant on both sides, left substitution in the
average of a translate and right substitution in the translate of the
average then give equal scalar evaluation integrals. This proves that
the character average commutes with every actual compact translation.

These are internally derived consequences of the weighted-average construction
and the published algebraic definition of the isotypic span. This module does
not yet show that the character average fixes its own type.
It assumes no Schur orthogonality, admissibility,
reproduction or automorphic differential growth result.
