# Reduced norms and cocycles for inner type A

Let \(A\) be a finite-dimensional central simple algebra over a field
\(F\). The definition `CentralSimpleUnits.affineReducedNorm` identifies
the affine points of the actual unit group of \(A\) with tensor units and
applies their reduced norm. It commutes with coefficient maps and takes
the inclusion of the actual reduced-norm-one group to the identity.

For \(F\) infinite and \(L/F\) finite Galois, `exists_cocycle_primitive`
takes a cocycle on \(\operatorname{Spec}L\) with values in the norm-one
group. It gives a point \(b\) of the unit group over \(L\) whose
coboundary is the image cocycle and whose reduced norm is the image of a
unit \(a\) of \(F\). The affine tensor-unit comparison transports the
Galois values to a crossed cocycle for the action on \(L\otimes_F A\).
Unit Hilbert 90 gives \(b\). Applying reduced norm to the coboundary
equation shows that its norm is Galois fixed, so it descends to \(a\).

If a point over \(F\) has the descended reduced norm, its extension is
Galois fixed. `isTrivial_of_primitive_norm` multiplies \(b\) on the right
by the inverse of this extension. The result has norm one and the same
coboundary, so it trivializes the original cocycle on the same cover.

Given an extension \(K/F\) and a finite Galois field \(M/K\) containing
compatible images of \(K\) and \(L\) over \(F\),
`exists_affineReducedNorm_of_baseChange_isTrivial` treats triviality on
the actual pullback cover to \(K\). Evaluation gives a norm-one
primitive \(y\) over \(M\). The ratio \(y^{-1}b\) is fixed by
\(\operatorname{Gal}(M/K)\), since its two factors come from primitives
of the same restricted cocycle. It descends to a unit group point
over \(K\), and its reduced norm is the image of \(a\) in \(K^\times\).

The construction implements the reduced-norm obstruction in
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
§2.3.1, Lemma 2.9, p. 80, and §6.7, pp. 356–357. It uses the
Library's coefficient-point descent and the actual norm-one scheme.
