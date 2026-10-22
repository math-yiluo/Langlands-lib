# Finite Laurent inequality neighborhoods

Author: Worker 36.

The module proves that every neighborhood of a point of the actual
multiplicative spectrum contains a compact finite Laurent inequality
locus with strictly positive thresholds, with the point in its interior.
It works for every normed commutative ring. It requires neither completeness
nor an ultrametric norm on that ring, and makes no assertion that its
spectrum is nonempty.

The source context is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), Definition 1.2.5, printed/PDF p.4, and Exercise
2.2.2(i), p.9, and (iv), p.10.
Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
[author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf).
The source gives the evaluation topology and, in the affinoid setting,
Laurent domains forming a fundamental system of neighborhoods. This module
proves the topological inequality-set component directly. Domain
representability is not used or asserted.

`finite_laurentLocus_mem_nhds` first handles finite tuples for which the
inequalities are strict at the chosen point: \(x(f_i)<r_i\) and
\(q_j<x(g_j)\). Continuity of each evaluation makes each corresponding
closed inequality a neighborhood. The intersection of the finitely many
neighborhoods is the specified Laurent locus.

For `exists_finite_laurent_neighborhood`, pull a given neighborhood back
from the function space using the actual evaluation embedding. A basic
product neighborhood restricts only a finite set \(S\) of ring elements.
For each of its coordinates choose a positive \(\epsilon_a\) such that
the closed real ball about \(x(a)\) of that radius lies in the prescribed
coordinate neighborhood.

Impose the upper bound \(y(a)\le x(a)+\epsilon_a\) for each \(a\in S\).
Impose the lower bound \(x(a)-\epsilon_a\le y(a)\) only on the finite
sublist \(T=\{a\in S:\epsilon_a<x(a)\}\).
Every upper threshold is positive by seminorm nonnegativity, and every
retained lower threshold is positive by the defining condition for \(T\).
At \(x\), all the inequalities are strict. For the omitted lower
inequalities, nonnegativity of \(y(a)\) already gives the required bound.
Consequently every point of the constructed locus lies in all the chosen
coordinate balls and hence in the original neighborhood.

The final theorem `exists_compact_finite_laurent_neighborhood` combines
this construction with the already proved compactness of closed Laurent
inequality subsets of the spectrum. Empty upper or lower lists are allowed.
The lists are finite subsets with their actual subtype indices, rather
than arbitrary infinite collections mislabeled as finite.

No weighted Tate algebra, analytic-domain universal property, structure
sheaf or atlas is assumed. Positive real thresholds in this topological
result do not supply the still-missing quotient constructions for arbitrary
radii.
