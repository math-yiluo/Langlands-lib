# Monic generators with pairwise coprime squarefree leading monomials

Setting: a field `k`, a monomial order `m`, and a finite family of `m`-monic polynomials
`g : γ → k[X_σ]` whose leading monomials `d j = m.degree (g j)` have pairwise disjoint
supports.

- `lvl m g D` is the `k`-span of the products `X^u g j` with `u + d j ≤ D`, and `lvlLT m g D`
  collects the elements of lower levels. `exists_mem_lvl`: every element of the ideal lies in
  some level. `degree_le_of_mem_lvl`: elements of level `D` have degree at most `D`.
- `exists_decomp`: an element of level `δ` is a lower-level element plus
  `Σ c j · X^(δ - d j) g j`, summed over the `j` with `d j ≤ δ`.
- `tm_sub_tm_mem_lvlLT` is the Koszul syzygy. For `j ≠ j'`,
  `X^(δ-d j) g j - X^(δ-d j') g j' = X^e (t_j g_j' - t_j' g_j)` with `t = g - X^d`, and this
  lies strictly below level `δ`.
- `mem_lvlLT_of_coeff_eq_zero`: if the coefficient at `δ` vanishes, the level drops.
- `exists_degree_le` (Buchberger's first criterion): every nonzero element of the ideal has
  a leading monomial divisible by some `d j`. The proof is by well-founded induction on the
  level.
- `isRadical`: if moreover every `d j` is squarefree, the ideal is radical. Divide `f` by `g`
  with `MonomialOrder.div` to get a remainder `r`. Then `r^N` lies in the ideal, some `d j`
  divides `N • deg r`, so `d j` divides `deg r` by squarefreeness, which contradicts the
  reduced remainder.

## Provenance

This is Buchberger's first criterion together with the standard fact that an ideal with
squarefree initial ideal is radical (Cox–Little–O'Shea, *Ideals, Varieties, and Algorithms*,
Ch. 2 §9, Prop. 4).
