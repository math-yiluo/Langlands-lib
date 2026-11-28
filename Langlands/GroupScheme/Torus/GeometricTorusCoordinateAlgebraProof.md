# The coordinate algebra of a torus over the algebraic closure

`geometricTorusCoordinateAlgebra` proves
`GeometricTorusCoordinateAlgebraStatement`. For a torus \(T\) over a field
\(F\), set \(K=\overline F\) and \(S=T_K\). Base change preserves the
torus property. The finite Galois splitting theorem gives \(S\) a finite
splitting extension of \(K\). Since \(K\) is algebraically closed,
`IsTorus.isSplitTorus_of_finiteGaloisSplitting` reflects splitness to \(K\).
The resulting split torus is affine.

Write \(A=K[X^*(S)]\) and \(B=\mathcal O(S)\). Let \(x\) be
`Lie.universalPoint` over \(B\) and \(y\) be
`SplitCharacterPoint.universalPoint` over \(A\). The algebra map
\(f\colon A\to B\) is `SplitCharacterPoint.pointLift x`, which sends the
monomial indexed by \(\chi\) to the value of \(\chi\) at \(x\).
The algebra map \(g\colon B\to A\) is the coordinate map of \(y\).

Changing coefficients in \(y\) along \(f\) gives \(x\) by
`SplitCharacterPoint.affineMap_pointLift`. Naturality of point
coordinates then gives \(f\circ g=\operatorname{id}_B\), since \(x\)
corresponds to the identity of \(B\). Changing coefficients in \(x\)
along \(g\) gives \(y\) by the defining property of \(x\). Naturality of
character evaluation and the prescribed values at \(y\) show that
\(g\circ f\) fixes each basis monomial of \(A\). The group-algebra
extensionality lemma gives \(g\circ f=\operatorname{id}_A\). Thus \(f\)
is the desired algebra equivalence and sends each monomial to its
character as a regular function on \(S\).

This is the geometric coordinate-algebra clause of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, § V.2.2, Remark 1, printed p. 105 (PDF p. 111).
The registered source is `renard-2026-representations-groupes-reductifs-padiques`
with SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
