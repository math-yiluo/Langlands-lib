# Full dynamic parabolics in pseudo-reductive groups

`Langlands.GroupScheme.PseudoReductiveCentralCocharacterStatement.{u}` is
the following proposition, for an arbitrary universe `u`. For every field
`k : Type u`, every pseudo-reductive group scheme `G` over `Spec k`, and
every actual cocharacter `χ : Gm.toGrp ⟶ G`,

```text
Dynamic.parabolic χ = ⊤ ↔ Dynamic.centralizer χ = ⊤.
```

Here pseudo-reductivity is the published `IsPseudoReductive G`: smoothness,
affineness, connectedness, and triviality of the ground-field unipotent
radical. The cocharacter is any group-scheme homomorphism from `Gm`; no
injectivity, nontriviality, split ambient group, perfect field, or
restriction on characteristic is imposed.

Both equalities concern the actual subgroup functors on every scheme over
`Spec k`. The parabolic consists of points whose conjugation orbit extends
across zero. The centralizer consists of points with constant conjugation
orbit, equivalently points commuting with the cocharacter after every
refinement of the test scheme. Thus the right side expresses centrality
of the cocharacter in the group scheme, rather than commutation of rational
points alone. Nonreduced tests are retained.

## Source

Conrad--Gabber--Prasad, *Pseudo-reductive groups*, second edition (2015),
source ID `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
Lemma 2.2.3(2) and its proof, printed pp. 62--63 / PDF pp. 88--89.
The source states the equivalent properness criterion: `P_G(χ)` is proper
as a subgroup precisely when the cocharacter is noncentral. The displayed
Lean formulation takes the logical complements of these two conditions.
The actual subgroup-functor definitions encode the associated
scheme-theoretic equalities.

The proof in the source first observes that a central cocharacter has full
parabolic. If the parabolic is full, its contracting subgroup is a smooth
connected unipotent normal subgroup of `G`. Pseudo-reductivity makes that
subgroup trivial; the limit decomposition then identifies the centralizer
with the full parabolic. The pseudo-reductivity hypothesis is essential,
as explained by the source's Example 2.2.2.

## Status and use

This file defines the proposition and does not prove it. In particular,
unipotence of the actual contracting subgroup is a proof obligation, not
an extra premise in this statement.

This is a geometric prerequisite for using noncentral cocharacters to
construct proper pseudo-parabolics in the rank-one root-kernel centralizer.
It supplies no reflection data, normalizing representative, or proof of
`RelativeRootReflectionExistenceStatement`.
