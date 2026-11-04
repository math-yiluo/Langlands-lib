# Natural coordinate transitions given by additive polynomials

This module is an internal step in the proof that every torus action on a vector
group becomes linear in suitable coordinates. In positive characteristic, the
new coordinates are obtained from the old ones by a tuple `Φ` of additive
polynomials in `n` variables with coefficients in the ground field `k`. Its
inverse is a second such tuple `Q`. This module turns such a pair into the
natural transition data of `Recoordinatize` and states the resulting linearity
criterion directly in terms of `Φ`, `Q` and the coordinate action. Everything is
in namespace `Langlands.GroupScheme.RelativeRoot`.

## The transition

`NaturalCoordinateEquiv.ofPolynomials Φ Q hΦ hQΦ hΦQ` takes
`Φ Q : Fin n → MvPolynomial (Fin n) k` and three hypotheses:

- `hΦ`: every `Φ i` is additive, `Φ i (x + y) = Φ i (x) + Φ i (y)`, for all
  vectors `x y : Fin n → B` over every commutative `k`-algebra `B : Type u`;
- `hQΦ`: substituting `Q` into `Φ` gives the variables, `Φ i (Q) = X i`;
- `hΦQ`: substituting `Φ` into `Q` gives the variables, `Q j (Φ) = X j`.

Over each `k`-algebra `A` the transition sends `x` to `fun i => Φ i (x)`, with
inverse `z ↦ fun j => Q j (z)`. The two inverse laws follow from `hΦQ` and `hQΦ`
by Mathlib's `MvPolynomial.comp_aeval_apply`: evaluating at `x` after
substituting `Φ` is evaluating at the values of `Φ` at `x`. Additivity is `hΦ`.
Naturality in `k`-algebra maps `f` is again `comp_aeval_apply`. Since the
coefficients lie in `k`, `f` commutes with evaluation.
`ofPolynomials_apply` and `ofPolynomials_symm_apply` unfold both directions.

## The criterion

Let `a` be an action of a group scheme `H` on `V`, with natural coordinates `e`.
`exists_isAffineLinear_of_polynomials` assumes `Φ`, `Q` as above, together with
`hlin`: for every `k`-algebra `B`, every point `t` of `H` over `B`, every scalar
`c : B` and every `y : Fin n → B`,

`Φ(act_t(Q(c • y))) = c • Φ(act_t(Q(y)))`,

where `act_t` is `coordinateAction a e t`, the action of `t` on coordinate
vectors. It concludes that there are coordinates `e'` that are natural and
satisfy the published `IsAffineLinearVectorCoordinates a e'`. The proof takes
`e' = recoordinatize e Y` with `Y = ofPolynomials Φ Q …`. Naturality is
`IsNaturalVectorCoordinates.recoordinatize`. Scalar linearity is
`isAffineLinearVectorCoordinates_recoordinatize`, whose hypothesis is `hlin`
after unfolding `coordinateAction` and `Y`.

## Provenance

This module is internal bookkeeping for the proof of
`TorusVectorActionLinearizationStatement`. It does not formalize a single
statement from the literature. It packages a change of coordinates by additive
polynomials, which is how this project realizes the new linear structure of
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed., Theorem B.4.3. The
source obtains that structure differently, through Propositions B.4.1–B.4.2. In
positive characteristic, homomorphisms `Ga^n → Ga` are exactly the maps given by
`p`-polynomials (Definition B.1.2 and Proposition B.1.3, printed p.562, PDF p.588),
which is why additive polynomials are the natural transition data here.
