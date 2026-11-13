# Descent of diagonal special-linear weights to a split torus

Author: Worker 187, Task 6023.

This internal adapter works over arbitrary fields `K` and `L` in the same
arbitrary universe, for any morphism `b : Spec L → Spec K`. Let `T` be an
actual split commutative group scheme over `Spec K`, let `n` be a finite index
type with a pivot `p`, and supply a commutative group homomorphism `q` from
the pullback of `T` to the standard special-linear diagonal torus over `L`.

`SpecialLinearTitsCocycle.descendedDiagonalWeight b T hT p q i` descends
`q ≫ SpecialLinear.diagonalWeight p (Spec L) i` through the inverse of the
published canonical additive equivalence
`characterLattice.baseChangeEquiv b T hT`. Its scalar extension is exactly
that character, as `baseChange_descendedDiagonalWeight` records.
`eq_descendedDiagonalWeight_sub` proves that any character whose scalar
extension is the difference of two such weights equals the corresponding
difference of the descended weights. The proof uses injectivity of the
canonical equivalence and additivity of pullback and precomposition.

For the matrix conclusion, additionally supply a group scheme `G`, an actual
`LocalGroupIso E` from the special-linear group over `K` to `G` over the
cover `Spec L`, and a homomorphism `f : T.toGrp → G`. The premise of
`diagonal_of_baseChangeFactorization` is the actual homomorphism equality

```
(baseChange b).map f ≫ E.toBaseChangeIso.inv ≫
  (SpecialLinear.baseChangeModelIso n b).hom =
    CommGroupScheme.groupHom q ≫ SpecialLinear.diagonalTorus p L.
```

Here `L` in the displayed model denotes its commutative-ring object. The
conclusion identifies the inverse local value of `s ≫ f`, on every original
relative test `Z` with any cover point `a`, with the diagonal matrix whose
entries are the evaluations of the descended characters at `s`.

The proof lifts `s` through the cover-point equivalence and applies the
factorization to that lift. Inverse local-isomorphism naturality and the
special-linear model comparison identify the resulting matrix with the
original inverse local value. The standard diagonal-weight formula and the
evaluation identity for base-changed characters then identify each entry.
The module proves both comparison identities used here:
`SpecialLinear.pointsEquiv_coverPointsEquiv` preserves each matrix entry,
and `characterLattice.pointsEquiv_baseChange_cover` preserves each unit.

This is a conditional adapter: it does not construct the diagonal
factorization, the root-matching identity, or the Galois presentation.
The general finite index type includes a singleton; no positive-rank,
characteristic, reduced-test, or rational-point restriction is imposed.

Provenance: derived from the published split-torus character equivalence,
the actual base-change special-linear model comparison, and the
diagonal-weight and cover-point identities. No classification theorem or
new original-literature assertion is used.
