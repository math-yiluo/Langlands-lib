# The uniform Lang–Weil estimate for families of curves, from the plane-curve bound

Author: Worker 69.

This module states a reduction: the uniform Lang–Weil estimate for families whose fibres are
geometrically irreducible curves follows from Schmidt's Hasse–Weil bound for absolutely
irreducible plane curves and the uniform upper bound for point counts in families. It is one
step of the Library's Lang–Weil route to Conrad's Lemma 4.6. The module contains no proof.

## The statement

`FamilyLangWeilCurveStatement` is the implication

`PlaneCurveHasseWeilStatement → FamilyPointUpperBoundStatement → FamilyLangWeilInDimension 1`,

all in the same universe `u`:

- `PlaneCurveHasseWeilStatement` (`Langlands/AlgebraicGeometry/LangWeil/PlaneCurveHasseWeilStatement.lean`):
  for a finite field with `q` elements and an absolutely irreducible `f ∈ F[X, Y]` of degree
  `m > 0` in `X` and `n > 0` in `Y`, `q > 9 (m + 1)² (n + 1)²` implies
  `|#{f = 0} − q| < 2 min(m² n, n² m) q^{1/2}`;
- `FamilyPointUpperBoundStatement` (`Langlands/AlgebraicGeometry/LangWeil/FamilyPointUpperBoundStatement.lean`):
  in a family of finite type over a base of finite type over `ℤ`, the points over a `κ`-point
  whose fibre has dimension at most `e` number at most `C (#κ) ^ e`;
- `FamilyLangWeilInDimension 1` (`Langlands/AlgebraicGeometry/LangWeil/FamilyLangWeilStatement.lean`):
  for a geometrically irreducible morphism of finite type over a base of finite type over `ℤ`
  whose fibres have pure dimension `1`, the points over every `κ`-point number
  `#κ + O((#κ)^{1/2})`, uniformly.

## Relation to the sources

Provenance: derived. This is the curve case of Lang–Weil in Terence Tao, *The Lang–Weil bound*
(registered source `tao-2012-lang-weil-bound`), Section 2, first paragraph: "If `V` is a plane
curve […] the claim follows directly from the Hasse–Weil bound. If `V` is a higher-dimensional
curve, we can use resultants to eliminate all but two of the variables (or, alternatively, one
can apply the primitive element theorem to the function field of the curve), and convert the
curve to a birationally equivalent (over `F`) plane curve, to reduce to the plane curve case
(noting that the singular points of the birational transformation only influence the number of
`F`-points by `O(1)` at most)." Here the plane-curve bound is Schmidt's (Acta Arith. 24 (1973),
Satz, printed p.347; registered source `schmidt-1973-zur-methode-von-stepanov`), and uniformity
in the family replaces Tao's bounded complexity.

Lang and Weil, *Number of points of varieties in finite fields* (Amer. J. Math. 76 (1954);
registered source `lang-weil-1954-number-of-points`), printed p.819 (PDF p.2), treat the case
`r = 1` of their Theorem 1 the same way, with a non-singular projective model `V_1` in place of a
plane model: the number of singular points of `V` and the number of points of `V_1` above each
are bounded in terms of the degree, so `|N_1 − N|` is bounded by a constant, and the Riemann
hypothesis for `V_1` (with `g ≤ (d − 1)(d − 2)/2`) gives `|N − q| ≤ 2g q^{1/2} + A + 1`. The
Library's route replaces Weil's Riemann hypothesis for curves, which needs the Riemann–Roch
theorem, by Schmidt's elementary bound for plane curves.

## Expected proof route

The proof is not part of this module. A natural route: by Noetherian induction it suffices to
treat a dense open of an integral affine piece of `S` and an affine open of `X` that is dense in
the fibres (the complement contributes `O(1)` points by the upper bound with `e = 0`). Over the
generic point, choose a birational plane model of the generic fibre (a separating transcendental
element and a primitive element of the function field, after a finite purely inseparable base
change if the generic fibre is not geometrically reduced; over finite fields such a base change
does not change point counts). Spread it out over a dense open of the base, so that the
comparison maps are isomorphisms outside finite exceptional loci and the plane equations stay
absolutely irreducible (the Library's generic spreading of geometric irreducibility, Stacks
0559). Apply Schmidt's bound when `#κ` is large and the upper bound with `e = 1` when it is small.

## Status

Open. A proof is to be supplied through its own focused proof task.
