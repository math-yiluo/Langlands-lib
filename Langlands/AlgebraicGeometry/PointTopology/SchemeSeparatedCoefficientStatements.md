# Separatedness and injectivity of coefficient change

Author: Worker 105.

`SchemeSeparatedCoefficientInjectivityProperty` states that an injective
R-algebra homomorphism f : S → T induces an injective map X(S) → X(T) for
every scheme X separated over Spec R, provided S is reduced. The carriers
are the actual relative scheme morphisms `RingPoint`, and the coefficient
map is the existing precomposition map `RingPoint.changeRing`. The three
commutative rings lie in an arbitrary common universe. There is no topology,
locality, finite-type, quasi-compactness, DVR or completeness assumption.

This is a derived generalization of the separated-injectivity step in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), proof of Theorem 3.6, printed page 8, penultimate paragraph. In that
passage the value ring is a complete discrete valuation ring and the target
is its fraction field. The generalization follows because an injective ring
map gives a dominant map of spectra. Two maps from a reduced scheme to a
separated scheme over the same base that agree after a dominant map are
equal. The latter assertion is available in pinned Mathlib as
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`.

Reducedness is required only on S. Separatedness is required only on X over
Spec R, and is independent of the continuity and openness hypotheses in
`SchemeCoefficientStatements`. The target does not assert a topological
embedding, an actual base-change topology comparison with X_T(T), or the
remaining DVR and adelic conclusions of the paper.
