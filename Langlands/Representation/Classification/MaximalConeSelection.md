# Selection of a dominance-maximal cone

Author: Worker 23.

This module is an internal helper for the proof of
`Langlands.GLMaximalConeJacquetQuotientStatement` (task b291a31b). Take a
finite family of block vectors in which at least one member has a cone. The
module selects a cone that no cone of any member strictly dominates, in the
sense of the published `Langlands.GLBlockPositivePartStrictlyDominates`. This
is the "choose a maximal element" step of Konno 2003, Theorem 3.5(i), made
explicit by a numerical potential. Cones are the structure
`MaximalConePolygon.IsCone` (module `MaximalConePolygon`), whose fields are
verbatim the six cone conditions of the target statement.

## Declarations

In namespace `Langlands.MaximalConePolygon`:

- `potential C t = ∑_{k = 0}^{n} pre (t ∘ (Geometric.blockIndex C)) k`: the sum of all prefix
  sums of the positive part `(C, t)` in standard coordinates.
- `potential_lt_of_strictlyDominates h`: if `(C₁, t₁)` strictly dominates
  `(C₂, t₂)`, then `potential C₂ t₂ < potential C₁ t₁`. Every prefix inequality
  is weak and one is strict, so `Finset.sum_lt_sum` applies.
- `coneValue B r C q j = (∑_{q i = j} r i) / C.size j`.
- `IsCone.eq_coneValue hc`: a cone has `t = coneValue B r C q`. Divide the
  block-total condition by the positive block size.
- `exists_maximal_cone R hR hne`. Let `R B` be a set of block vectors along each
  `B : BlockShape n`, each `R B` finite, and suppose some `r ∈ R B` has a cone.
  Then some `r ∈ R B` has a cone `(C, q, t)` such that no cone `(C', q', t')` of
  any `r' ∈ R B'` strictly dominates `(C, t)`.

## Proof of `exists_maximal_cone`

The set `V` of potentials of all cones of members of the family is finite. There
are finitely many block shapes (the published instance
`GeneralLinear.BlockShape.finiteBlockShape`, module
`Langlands.Representation.CuspidalSupport.FiniteBlockShapes`). Each `R B` is
finite, and there are finitely many maps `q`. Each cone value is
`coneValue B r C q`, so `V` lies in the finite union of the values
`potential C (coneValue B r C q)`. `V` is nonempty by hypothesis. Choose a cone
whose potential is maximal in `V` (`Set.exists_max_image`). A strictly
dominating cone would have strictly larger potential
(`potential_lt_of_strictlyDominates`), contradicting maximality.

In the proof of the target, `R B` is the set of real parts of the dual
exponents of `A` along `B`. It is finite because there are finitely many dual
exponents (the published dual-exponent finiteness statement) and real parts are
unique (`IsRealPartOf.eq`). A first cone comes from the one-block exponent
(module `MaximalConeExponents`).

## Sources

T. Konno, *A note on the Langlands classification and irreducibility of induced
representations of p-adic groups* (2003), registered as
`konno-2003-langlands-classification`, Theorem 3.5(i) (pp.396–397): choose an
exponent whose positive part is maximal for the dominance order (order on
p.394). The potential function is the Lean device for this choice and is not
taken from the source.
