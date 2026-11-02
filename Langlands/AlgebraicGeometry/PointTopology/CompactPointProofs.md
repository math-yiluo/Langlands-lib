# Compactness through finite coordinates and a finite affine cover

The entry theorem proves exactly `CompactValueRingPointProperties R S` in
`CompactPointStatements`, retaining the separate local-ring hypothesis for
the nonaffine branch.

For a finite-type coordinate algebra, choose its presentation as a quotient of
a polynomial algebra in finitely many variables. The published polynomial
point homeomorphism and surjective-precomposition closed embedding embed its
actual algebra points as a closed subspace of a finite power of the compact
Hausdorff topological value ring. This makes the algebra-point space compact.
The actual affine scheme point homeomorphism transfers compactness to the
existing relative scheme points and their evaluation topology.

For a quasi-compact locally finite type scheme, Mathlib supplies a finite
affine open cover of its underlying space. Each affine chart remains locally
of finite type over the base, so the first part makes its point space compact.
The point-chart maps are continuous directly from the definition of
`schemePointTopology`; no open-unit or inversion theorem is used.
For every actual point, the image of the closed point of the local value ring
lies in one of these finitely many affine opens. The existing local-ring
factorization theorem lifts the entire point into that chart. Thus the whole
point space is a finite union of compact chart images and is compact.

The proof covers the compact-value-ring prerequisite described in the target
Markdown. The valuation-ring realization, algebraic-space and comparison
obligations of Corollary 5.7 remain separate.
