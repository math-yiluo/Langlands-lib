# Rational points of linked root parametrizations satisfy the rank-one relation

Author: Worker 4348.

Module `Langlands.GroupScheme.Reductive.LinkedRootRationalRelation`, namespace
`Langlands.GroupScheme.LinkedRootParametrization`.

Let `k` be a field and `G` an affine group scheme over `Spec k`. Let `i : T ⟶ G` be a torus
map, `α` a character and `ν` a cocharacter of `T`, and
`X : LinkedRootParametrization i α ν` the Library's linked parametrization of the root
groups of `±α` (module `Reductive.LinkedRootParametrization`). This module evaluates `X`
on rational points. It shows that the values form the abstract rank-one relation data
`Langlands.Algebra.RankOneRelation.Data` of module `Algebra.RankOneRelationIdentities`.

## Definitions

- `secMap k : k →+* Γ(Spec k, ⊤)` is the inverse of the Library isomorphism
  `Scheme.ΓSpecIso`. It identifies `k` with the global sections of `Spec k`.
- `cocharacterPoint i ν : kˣ →* rationalPoints G`. A unit `t` goes to the rational point
  `ν(t)` of `T`, built from `Gm.pointsEquiv` and `secMap`, followed by `i`. Multiplicativity
  follows from `MonObj.one_comp` and `MonObj.mul_comp`.
- `X.xpPoint c` and `X.xmPoint c` are the rational points `x₊(c)` and `x₋(c)`. Each is the
  point `gpt (secMap k c)` of the additive group, composed with `X.positive` and
  `X.negative` respectively.

## Results

- `xpPoint_add`, `xmPoint_add`: additivity, from `gpt_add` and `MonObj.mul_comp`.
- `relation_rational a b u hu`: for a unit `u` with `u = 1 + a b`,
  `x₊(a) x₋(b) = x₋(u⁻¹ b) ν(u) x₊(u⁻¹ a)`. This is the field `X.relation`, which is
  `RootCell.RelationOver`, applied at the identity test scheme to the points with
  coordinates `secMap a`, `secMap b`, `secMap (u⁻¹ a)` and `secMap (u⁻¹ b)`. The
  coordinate side conditions are discharged by `simp` from `hu`.
- `cu_cocharacter t`: on the point `ν(t)`, the character `α` has the unit value
  `t ^ ⟨α, ν⟩`, transported by `secMap`. The proof writes `ν ≫ α` as
  `⟨α, ν⟩ • 𝟙`, using `eq_gmEndEquiv_zsmul` and `latticePairing_apply`, then applies
  `comp_groupHom_zsmul`.
- `cocharacterPoint_conj_xmPoint h2 t c`: if `⟨α, ν⟩ = 2`, then
  `ν(t) x₋(c) ν(t)⁻¹ = x₋(t⁻² c)`. This is the field `X.negative_equivariant`, weight `-α`,
  at the point `ν(t)`. Its character value is computed with `charValue_eq_cu`, `cu_neg`
  and `cu_cocharacter`.
- `rankOneData h2`: the structure `RankOneRelation.Data k (rationalPoints G)` with
  `xp = X.xpPoint`, `xm = X.xmPoint` and `h = cocharacterPoint i ν`, assuming
  `⟨α, ν⟩ = 2`.

Consequently every identity of `Algebra.RankOneRelationIdentities` holds for these
rational points. In particular `h_eq_word` writes `ν(u)` as a word in `x₊` and `x₋`, and
`w_mul_w_one_inv` gives `w(v) w(1)⁻¹ = ν(v)`.

## Provenance

This is internal glue between the Library's linked root parametrizations and the abstract
rank-one identities. It introduces no new mathematical assertion.
