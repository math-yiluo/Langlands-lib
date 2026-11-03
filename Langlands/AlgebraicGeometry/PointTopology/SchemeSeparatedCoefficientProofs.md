# Injectivity of actual separated scheme points under coefficient change

Authors: Worker 105 (Lean proof and first Markdown); Worker 1116 (Markdown
revision and submission).

This proof targets exactly
`SchemeSeparatedCoefficientInjectivityProperty R S T`, for arbitrary
commutative rings R, S, T in a common universe, R-algebra structures on S and
T, and reduced S. The theorem `schemeSeparatedCoefficientInjectivity_proof`
proves it with no further hypotheses.

## Auxiliary result

`isDominant_ringTestMap` proves that an injective R-algebra map f : S → T
induces a dominant map Spec(T) → Spec(S); this is the underlying scheme map
`(ringTestMap R f).left`. Its underlying continuous map is
`PrimeSpectrum.comap f`. Mathlib's
`PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical` says that this map has
dense range exactly when the kernel of f lies in the nilradical of S.
Injectivity makes that kernel zero, so the condition holds.

## Main proof

Let X be a scheme over Spec R with separated structure map, let f be an
injective R-algebra map, and let p, q be actual relative S-points of X with
equal images under `RingPoint.changeRing f`. The images are the composites
`ringTestMap R f ≫ p` and `ringTestMap R f ≫ q`. Taking underlying scheme
maps, `(ringTestMap R f).left ≫ p.left = (ringTestMap R f).left ≫ q.left`.

The commutative triangles of p and q over Spec R (`Over.w`) show that
`p.left ≫ X.hom` and `q.left ≫ X.hom` both equal the structure map of
Spec(S). Spec(S) is reduced because S is reduced. Mathlib's
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated` says that two maps from
a reduced scheme to a scheme separated over a base, which agree over the base
and agree after composing with a dominant map, are equal. So
`p.left = q.left`, and `RingPoint.ext` gives p = q.

No topology, locality, finiteness, domain or completeness assumption is used.
The source motivation and how this generalizes Conrad's DVR setting are
recorded in the target Markdown `SchemeSeparatedCoefficientStatements.md`.
