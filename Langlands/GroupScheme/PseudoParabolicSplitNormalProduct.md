# A normal split product inside a supplied pseudo-parabolic

Author: Worker 60.

This is a derived construction over every field `k : Type u`, for a smooth
affine group scheme `G`, a cocharacter `χ`, a supplied split ground-field
unipotent radical `n : V → G`, and a supplied represented product
`i : P → G` of `P_G(χ)` with `range n`. The split-product presentation
is an explicit hypothesis of this construction. This module does not
replace a product with the ordinary radical by one with the split radical.

`NormalProduct χ n i` records an actual group scheme `D` and a closed
inclusion `q : D → P`, such that `q ≫ i` represents the fppf-local product
`U_G(χ) R_us,k(G)`. It records smoothness, connectedness, unipotence,
split unipotence in the existing finite represented Ga-series sense, and
normality of `range q` in `P` on all relative tests.

`normalProduct` constructs these objects. The published affine dynamic
representative of `U_G(χ)` is smooth and connected, and the published
dynamic splitness theorem makes it split unipotent. Apply
`SplitNormalFactorProduct.product` to this representative and `n`,
using ambient normality only for `range n`. The resulting actual
smooth connected split-unipotent product `d : D → G` lies in `range i`
by leastness of represented fppf products, since `U_G(χ) ≤ P_G(χ)`
and both factors lie in `range i`. The represented-subgroup factor
construction gives `q` with `q ≫ i = d`, and closedness reflects along
the closed monomorphism `i`.

For normality, `P_G(χ)` normalizes `U_G(χ)` by the dynamic conjugation
lemma and normalizes `range n` by its ambient normality. The relative
normalization law for represented products then shows it normalizes
`range d`. Also `range n` normalizes `range d`, because it is contained
there. As `P` is the represented fppf-local product of these two
normalizing subgroups, fppf membership descent shows that `range i`
normalizes `range d`. Cancel the monomorphism `i` to obtain normality
of `range q` inside `P`. This argument never asserts that the ordinary
ground-field radical normalizes `U_G(χ) R_us,k(G)`.

`containment` takes any supplied split ground-field unipotent radical
`m : W → P`. Its greatestness contains the constructed closed smooth
connected split-unipotent normal subgroup `q`. Mapping that containment
through `i`, and applying the two factor containments of the represented
product `q ≫ i`, gives

```lean
Dynamic.unipotent χ ≤ SubgroupFunctor.range (m ≫ i) ∧
  SubgroupFunctor.range n ≤ SubgroupFunctor.range (m ≫ i)
```

Both inequalities hold on every relative scheme test, including
nonaffine and nonreduced tests. Factorization of product points is allowed
only after an fppf cover; no local section or factorization on the
original test is supplied as a premise.

The construction implements the product-normality and maximality steps
in the first paragraph of the proof of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Corollary 2.2.5,
printed p.64 (one-based PDF p.90). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The finite-series product construction reuses the existing split
semidirect induction in place of explicitly forming a quotient of
`U_G(χ)`, as in the source's use of Proposition A.1.4. The independent
Proposition 2.2.4 obligation needed to derive the split-product
presentation from the ordinary-radical presentation remains outside this
module.
