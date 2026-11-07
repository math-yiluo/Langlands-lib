# Rank-one degree bounds for actual covariant coordinates

This is derived supporting work by Worker 1369. It constructs the polynomial
of an actual affine-line curve in an affine group and proves a degree bound
from supplied all-test rank-one relations and coordinate covariance. The
argument uses the actual coordinate evaluation and relative-spectrum counit
already in the Library; it introduces no external source assertion.

## Reciprocal polynomials

Over an infinite field, `natDegree_le_of_reciprocal` proves that
`Q(t) = t^m P(t⁻¹)` for every nonzero scalar forces `P.natDegree ≤ m`.
If the degree were larger, the polynomial identity
`P.reverse = X^(P.natDegree - m) * Q` follows from equality on the infinite
set of nonzero scalars. Its constant coefficient would say that the nonzero
leading coefficient of `P` is zero. The zero polynomial is covered by the
same conclusion.

`reciprocal_transition` starts from `RootCell.RelationOver i nu xp xm Z`
on an arbitrary relative test scheme `Z`. Writing `h(z)` for the point of
the group obtained from the cocharacter `nu` and inclusion `i`, it proves

```
xm(1) xp(z - 1) = xp(z⁻¹ (z - 1)) h(z⁻¹) xm(z⁻¹)
```

for every unit global section `z`. The implemented proof applies the supplied
relation to parameters `-(z - 1)` and `-1`, then inverts it. It uses the
actual group operation and actual additive-line points. No rational-point
restriction is imposed on this transition theorem.

## Actual curve coordinates

Let `G` be an affine group scheme over a field `k` in arbitrary universe `u`.
`sectionValue` is actual coordinate evaluation with global-section codomain
explicit. For every commutative coefficient algebra `A`, `affineValue`
composes `pointAlgebraHom` with the inverse of `specCounitEquiv A`, so its
values lie in `A`. `affineValue_naturality` proves compatibility with any
coefficient-algebra homomorphism using the proved counit naturality.

For an arbitrary relative-scheme morphism `a : Ga → G`,
`curvePolynomial G a` is an algebra homomorphism from the actual coordinate
algebra of `G` to `k[X]`. It applies `affineValue` to `a` in the one-variable
coordinate algebra of `Ga` and then uses the multivariate-to-univariate
polynomial equivalence. The curve need not be a group homomorphism.
`curvePolynomial_aeval` identifies its evaluation at every element of every
commutative coefficient algebra with actual curve evaluation. The lemmas
`affinePoint_eq_pt` and `curvePolynomial_eval` compare this formula with the
global-section parameter used in the rank-one relation.

For a fixed `k`-point `g` of `G`, `negativeCurve` is the actual curve
`s ↦ xm(s) g`, and `transitionCurve` is the actual regular curve
`s ↦ xm(1) xp(s - 1) g`. Their point formulas hold on every relative test
scheme, with `g` pulled back along its structure map.

## Covariant degree bound and retained obligations

`natDegree_negativeCurve_le` assumes that `k` is infinite, that `xp` and
`xm` are actual additive-group homomorphisms with the supplied rank-one
relation on every relative test scheme, and that a coordinate `b` is
invariant under left multiplication by `xp` and transforms under `h(z)`
by `z⁻ᵐ`, also on every relative test scheme. It proves that the actual
polynomial of `s ↦ b(xm(s)g)` has degree at most `m`, for every `k`-point
`g` and every natural `m`.

The proof applies the transition at each nonzero scalar `t`. Positive-root
invariance removes its first factor and coroot covariance gives
`Q(t) = t^m P(t⁻¹)`. Counit injectivity transfers this equality to `k`,
and the reciprocal polynomial lemma supplies the degree bound.

The relation and both covariance laws are explicit hypotheses. This unit
does not prove that a specified covariant character has these laws, extend
the final degree conclusion to arbitrary coefficient-algebra points, or
construct a Steinberg representation. The Frobenius cutoff, whole-space
restriction injectivity, sharp dimension bound, structural existence and
`SteinbergBigCellStatement` remain obligations of the host task.
