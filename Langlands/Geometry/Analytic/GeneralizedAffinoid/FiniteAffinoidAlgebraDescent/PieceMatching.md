# Matching families of restricted local pieces over full domains

This module contains internal definitions and elementary lemmas for the
proof of `FiniteAffinoidAlgebraGlobalGenerationStatement`. They concern the
Library's finite affinoid algebra descent interface. All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent`.

Throughout, `K` is a complete ultrametric normed field (trivial valuations
allowed), `R` an actual presented affinoid algebra, `c` a finite full-domain
cover of `Domain.whole K R`, `F : LocalAlgebras c` the finite local algebras,
and `t : PairTransitions F` the pairwise transitions. The triple cocycle is
not used here.

## Lemmas on the given interface

- `LocalAlgebras.restrict_comp` and `restrict_restrict`: the Library's
  restrictions `F.restrict i` between closed-quotient base changes compose
  along `E ⊆ D ⊆ G`. Proof: uniqueness of maps out of the affinoid pushout
  (`AffinoidPushout.hom_ext`), checked on both legs with `restrict_localMap`,
  `restrict_baseMap` and `restriction_comp`.
- `PairTransitions.transition_localMap'`: the Library's `transition_localMap`
  restated with an explicit overlap containment.
- `PairTransitions.restrict_transition`: transitions commute with
  restriction to a smaller full domain `E ⊆ D`. Proof: uniqueness of maps out
  of the pushout, checked on both legs.

## Pieces and matching families

For a full domain `V` of `R`:

- `piece V i = F.baseChange i (V.inter (c.obj i)) _`: the `i`-th local algebra
  changed to the literal intersection of `V` with the `i`-th cover member.
- `pieceRestrict h i`: the restriction `piece V i → piece V' i` along a locus
  containment `h : V' ⊆ V`, namely `F.restrict i`.
- `IsMatching V m`: a family `m i ∈ piece V i` matches if, for all `i, j` and
  every full domain `E` contained in both `V ∩ cᵢ` and `V ∩ cⱼ`, the restricted
  transition `t.transition i j E` sends the restriction of `m i` to `E` to the
  restriction of `m j` to `E`. Quantifying over all such `E`, rather than only
  the literal triple intersection, makes restriction to smaller domains
  immediate.
- `pieceMatching V`: the `K`-subalgebra of the product of the pieces
  consisting of matching families. For `V = Domain.whole K R` it is the
  domain-level analogue of the Library's `MatchingAlgebra`.
- `matchingRestrict h`: the induced `K`-algebra map
  `pieceMatching V → pieceMatching V'` for `V' ⊆ V`, which applies
  `pieceRestrict` to each component. It preserves matching by
  `restrict_restrict`.
- `matchingStructure V`: the `K`-algebra map from `V.algebra` to
  `pieceMatching V`. Its `i`-th component is the restriction to `V ∩ cᵢ`
  followed by the pushout leg `F.baseMap i`. The image matches by
  `restrict_baseMap`, `restriction_comp` and `transition_baseMap`.
- `Generates V s`: the finite family `s` generates `pieceMatching V` as a
  module over `V.algebra` through `matchingStructure V`. That is, every
  matching family equals `∑ₖ matchingStructure V (aₖ) * sₖ` for some
  coefficients `aₖ ∈ V.algebra`.
- `PiecesGenerate V s`: for every index `i`, the `i`-th components
  `(s k).val i` generate the piece `piece V i` as a module over the algebra of
  `V ∩ cᵢ`, acting through the pushout leg `F.baseMap i`. That is, every
  `p ∈ piece V i` equals `∑ₖ F.baseMap i _ _ (aₖ) * (s k).val i` for some
  coefficients `aₖ` in the algebra of `V ∩ cᵢ`. This condition concerns each
  local finite algebra separately and does not refer to the transitions.

## Provenance

These are internal definitions of this project, encoded through the Library's
`baseChange`, `restrict` and `transition` maps. For arbitrary `PairTransitions`,
`pieceMatching V` is only the equalizer of the pieces over `V` under the
supplied transitions on all common full subdomains. No sheaf-theoretic or
finite-module interpretation of it is claimed in this generality. For example,
a self-transition `t.equiv i i` that is not the identity, such as the swap of
the factors of `A × A`, cuts the matching families down to a proper subalgebra
of what gluing the local algebras would produce.

When the transitions come from `DescentData`, that is, with the identity and
the triple cocycle, the matching condition with `i = j` holds automatically. By
`restrict_transition` it is enough to impose the other conditions on the
literal intersections `(V ∩ cᵢ) ∩ (V ∩ cⱼ)`. Then `pieceMatching V` is the
section equalizer of the descended finite algebra over `V`, as in Kiehl's
theorem: Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), Kiehl's Theorem and Remark 1.2.1(ii), printed p.15 / PDF p.12
(registered source `berkovich-1993-etale-cohomology`). This identification is
background only: it is neither formalized nor used here, and the definitions
and lemmas above use no cocycle.
