# The split form of a reductive group: statement

Worker 3483.

`Langlands.GroupScheme.SplitFormStatement.{u}` is a proposition definition. This
module does not prove it.

## The statement

Let `k` be a field in the universe `u` and `k_s = SeparableClosure k`. Base change to
`k_s` is `GroupScheme.baseChange (algebraBaseMap k k_s)`, written `(-)_{k_s}` below.
For every group scheme `G` over `Spec k` with `IsConnectedReductive G`
(`Reductive/Basic`) the statement asserts:

1. **Existence.** There are a group scheme `G₀` over `Spec k`, a commutative group
   scheme `T₀` over `Spec k` and a homomorphism `i₀ : T₀ ⟶ G₀` such that
   `IsConnectedReductive G₀`, `IsSplitTorus T₀` (`Torus/Split`), `IsMaximalTorus i₀`,
   and `G₀_{k_s} ≅ G_{k_s}` as group schemes over `Spec k_s`.
2. **Uniqueness.** If `G₁` and `G₂` are connected reductive over `k` with maximal tori
   `i₁ : T₁ ⟶ G₁` and `i₂ : T₂ ⟶ G₂` that are split tori, and both `G₁_{k_s}` and
   `G₂_{k_s}` are isomorphic to `G_{k_s}`, then `G₁ ≅ G₂` over `k`.

A connected reductive group with a split maximal torus is a split reductive group in
Milne's sense. So the statement says that every connected reductive group over `k` has a
split form, unique up to isomorphism.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over a
Field* (2017), source ID `milne-2017-algebraic-groups`.

Corollary 23.57 (printed p.501, PDF p.517):

> COROLLARY 23.57. Let G be a reductive group over k. There exists a split reductive
> group G_0 over k, unique up to isomorphism, such that G_{0 k_s} ≃ G_{k_s}.

Its proof (same page):

> PROOF. Let T be a maximal torus in G. Then T_{k_s} is a split maximal torus in
> G_{k_s} (see 17.82), and we take (G_0, T_0) to be the split reductive group over k
> with root datum equal to that of (G, T)_{k_s}.

The definition of a split reductive group (§21.a, printed p.424, PDF p.440):

> Recall also that G is split if some maximal torus T is split, in which case we refer
> to the pair (G, T) as a split reductive group.

## Correspondence with the source

- Milne's reductive groups are connected group varieties (6.46, printed p.135,
  PDF p.151: "A connected group variety over a field k is said to be reductive if
  G_{k^a} is reductive, i.e., if its geometric unipotent radical R_u(G_{k^a}) is
  trivial."). The Library's `IsConnectedReductive` (smooth, affine, connected, trivial
  geometric unipotent radical) is the corresponding notion.
- "Split reductive group `G₀`" is expressed by a maximal torus `i₀ : T₀ ⟶ G₀` with
  `IsSplitTorus T₀`, following Milne's definition quoted above.
- "`G_{0 k_s} ≃ G_{k_s}`" is an isomorphism of the base changes along
  `Spec k_s → Spec k` with `k_s = SeparableClosure k`.
- "Unique up to isomorphism" is part 2: any two split connected reductive groups over
  `k` whose base changes to `k_s` are isomorphic to `G_{k_s}` are isomorphic over `k`.
  The statement does not ask the isomorphism to respect the chosen tori.

## Relation to the Library

- Milne's proof combines the existence theorem (23.55), the isomorphism theorem
  (23.25), existence of maximal tori and their splitting over `k_s` (17.82). The
  Library has `splitReductiveExistence : SplitReductiveExistenceStatement`
  (`Reductive/SplitExistence`, existence of a split group with a prescribed reduced
  root datum), `splitCommonTorusIsomorphism : SplitCommonTorusIsomorphismStatement`
  (`Reductive/SplitIsomorphismProof`, the isomorphism theorem for two groups with a
  common split maximal torus and matching root data) and
  `maximalTorusExistence : MaximalTorusExistenceStatement`
  (`Torus/ExistenceProof`).
- No Lean declaration of Corollary 23.57 was found: searching `Langlands/` for
  `SplitForm` and for statements with conclusions `Nonempty (G₀_{k_s} ≅ G_{k_s})`
  found none. The published family-7 ledger
  (`notes/group-schemes/ledger-family-7-split-classification.md`) records the
  existence theorem (row A1) and the common-torus isomorphism theorem (row A2) but no
  split-form row.
