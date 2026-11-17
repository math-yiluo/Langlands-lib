# Compact bi-invariant envelopes of actual matrix heights

This internal supporting construction for Waldspurger II.3.5 and VIII.3.1
takes the supremum of the original matrix height over the double coset of
a specified compact subgroup. It supplies an auxiliary real-valued height
function; it does not assert that the originally supplied matrix height is
invariant under that subgroup, or that the envelope is itself the matrix
height of another representation. Distinct compact subgroups remain
distinct throughout.

For a group `H`, subgroup `K`, and real function `σ`,
`compactHeightEnvelope K σ g` is the real supremum of
`σ(k * g * l)` over `(k,l) : K × K`. The set of values is nonempty.
The comparison lemmas explicitly assume subadditivity and a bound
`σ(k) ≤ D` for `k ∈ K`; they prove boundedness before using the
conditional completeness of the real supremum. These assumptions give

```text
σ(g) ≤ compactHeightEnvelope K σ g ≤ σ(g) + 2 * D.
```

Translation within `K` reindexes the same double coset, proving exact
bi-invariance. Inversion reindexes the factors and uses inversion
invariance of `σ`. To prove subadditivity, split each representative of
`K * (g*h) * K` as `(k*g) * (h*l)` and bound the two terms by the
envelopes at `g` and `h`. There is no assertion that the envelope
vanishes at the identity.

For an open subgroup, bi-invariance makes the envelope locally constant
on right cosets. This fact needs no regularity assumption on `σ`.
`eventually_rationalCompactHeight_eq_and_conj` gives simultaneous
eventual equality at a point and its conjugate, exactly in the form used
by the density step of the generic `mem_mul_of_dense` open-cell lemma.

The actual rational-point construction uses continuity of the given
matrix height to bound its compact translation factors. Its main names
are:

- `rationalCompactHeight ρ K`, the envelope of `rationalHeight ρ`;
- `exists_rationalHeight_le_on_compact`, a nonnegative bound `D`;
- `rationalCompactHeight_bounds`, the additive comparison above and
  `1 + rationalCompactHeight ρ K g ≤ (1 + 2*D) * (1 + rationalHeight ρ g)`;
- `rationalCompactHeight_nonneg`, `rationalCompactHeight_mul_mul`,
  `rationalCompactHeight_inv`, and `rationalCompactHeight_mul_le`;
- `isLocallyConstant_rationalCompactHeight` for open `K`.

The seminorm comparison is explicit. If
`1 + τ(g) ≤ A * (1 + σ(g))` for nonnegative heights, `A ≥ 0`, and
positive `Ξ`, then

```text
ν_r(Ξ,τ)(f) ≤ ofReal(A ^ max(r,0)) * ν_max(r,0)(Ξ,σ)(f).
```

The proof first increases the exponent to `max(r,0)`, then applies the
height comparison to this nonnegative exponent. Multiplicativity of real
powers and the definition of the extended seminorm give the result.
`all_nu_lt_top_of_one_add_height_le_mul` transfers finiteness of all
seminorms. Applying this in both directions proves
`rationalCompactHeight_levelSubmodule_eq` for every original
bi-invariance subgroup and `rationalCompactHeight_schwartzSubmodule_eq`
for the full underlying Schwartz submodule. The positive spherical
weight is fixed in these equalities; only the auxiliary height varies.

These results need no closedness, height-adaptation, reductivity, torus,
Cartan, or Iwasawa hypothesis. They apply to any nonempty finite matrix
index type over every nonarchimedean local field in an arbitrary field
universe. The additional theorem `isCompact_rationalCompactHeight_le`
uses a closed matrix realization indexed by nonempty `Fin N`, and
compact open `K`, to prove compactness of every envelope sublevel. Its
proof combines continuity from local constancy with
`rationalHeight ≤ rationalCompactHeight` and the published compactness
of the original matrix-height sublevels.

This is an elementary auxiliary construction derived from the published
matrix-height properties and compactness. It is not a translation of a
separately named assertion in the literature. The motivating original is
Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, Lemma II.3.5, proof step (3), printed p.259,
and Proposition VIII.3.1, printed pp.323–326 (registered
`waldspurger-2003-plancherel`). The construction supplies comparison and
compact invariance; the remaining coordinate growth, contraction, and
integral estimates remain separate obligations.
