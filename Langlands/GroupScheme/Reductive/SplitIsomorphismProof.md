# Proof: the Isomorphism Theorem for split reductive groups with a common maximal torus

Authors: Worker 712, Worker 1444.

This module proves the published proposition
`Langlands.GroupScheme.SplitCommonTorusIsomorphismStatement`
([`Reductive.SplitIsomorphismStatement`](SplitIsomorphismStatement.md)) at its
original universe `u`. Let `k` be a field, `G₁` and `G₂` connected reductive
group schemes over `Spec k`, `i₁ : T ⟶ G₁` and `i₂ : T ⟶ G₂` split maximal
tori with the same `T`, and `P₁`, `P₂` root data of `i₁` and `i₂` that have the
same roots and coroots after a reindexing `e : J₁ ≃ J₂`. Then there is an
isomorphism `ψ : G₁ ≅ G₂` with `i₁ ≫ ψ.hom = i₂`. This is the Isomorphism
Theorem of Milne, *Algebraic Groups* (2017), Theorem 23.25 and Remark 23.26, in
the case of a common split maximal torus and the identity of the character
lattice. The module proves nothing beyond that statement and adds no axioms.

## Declarations

- `splitCommonTorusLeviGluing : SplitCommonTorusLeviGluingStatement.{u}`: the
  gluing step ([`Reductive.SplitLeviGluingStatement`](SplitLeviGluingStatement.md))
  holds over every field.
- `splitCommonTorusIsomorphism : SplitCommonTorusIsomorphismStatement.{u}`: the
  target.

Both theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.

## Proof

The proof only combines published Library results.

`splitCommonTorusLeviGluing` is
`LeviGluing.splitCommonTorusLeviGluing_of_algClosedGraphs` applied to
`LeviGluing.algClosedGraphProjectionIsomorphisms`.

- `splitCommonTorusLeviGluing_of_algClosedGraphs`
  ([`Reductive.SplitLeviGluingDescent`](SplitLeviGluingDescent.md), Worker
  1444) derives the gluing statement over any field from the internal
  proposition `AlgClosedGraphProjectionIsomorphisms`. That proposition says
  that, over an algebraically closed field, both projections of the comparison
  graph of the two groups are isomorphisms. The descent from an algebraic
  closure, the construction of the graph and its local comparisons are in the
  modules that this one imports.
- `algClosedGraphProjectionIsomorphisms`
  ([`Reductive.SplitLeviGluingFactorInjectivity`](SplitLeviGluingFactorInjectivity.md))
  proves that proposition. The differential of each projection is injective,
  checked one torus weight at a time, and an injective differential makes the
  unipotent factor maps isomorphisms.

`splitCommonTorusIsomorphism` is
`splitCommonTorusIsomorphism_of_rankOne_of_leviGluing
splitRankOneCommonTorusIsomorphism splitCommonTorusLeviGluing`.

- `splitCommonTorusIsomorphism_of_rankOne_of_leviGluing`
  ([`Reductive.SplitIsomorphismCentralizerRootData`](SplitIsomorphismCentralizerRootData.md))
  derives the target from the rank-one statement
  `SplitRankOneCommonTorusIsomorphismStatement` and the gluing statement. The
  gluing statement asks for isomorphisms of the centralizers of those
  cocharacters `ν` of `T` for which any two roots orthogonal to `ν` are
  linearly dependent. These centralizers are connected reductive by
  `dynamicCentralizerReductive`. Their roots are the roots orthogonal to `ν` by
  `dynamicCentralizerRoots`. The restrictions of `P₁` and `P₂` to those roots
  are root data of the centralizers. The rank-one statement then gives the
  centralizer isomorphisms.
- `splitRankOneCommonTorusIsomorphism :
  SplitRankOneCommonTorusIsomorphismStatement.{u}`
  ([`Reductive.SplitRankOneIsomorphismProof`](SplitRankOneIsomorphismProof.md),
  Workers 239 and 1388) is the rank-one case without hypotheses. It handles
  rank zero directly. In rank one it builds the root groups and the open cell
  of both groups for the same root and coroot, and glues the isomorphism from
  the open cells.

## Route

Milne proves Theorem 23.25 by reducing it to groups of semisimple rank one
(Proposition 23.14) and gluing along the subgroups of semisimple rank one
through the graph of the two groups (23.15-23.24). The implemented proof has
the same overall shape. The subgroups of semisimple rank at most one are the
centralizers of cocharacters `ν` for which any two roots orthogonal to `ν` are
linearly dependent. The graph argument is carried out over an algebraic
closure and then descended to `k`. The individual steps
are described in the Markdown of the modules linked above.
