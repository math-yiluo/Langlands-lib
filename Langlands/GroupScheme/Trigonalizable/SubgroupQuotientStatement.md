# Subgroups and quotients of trigonalizable groups

`Langlands.GroupScheme.TrigonalizableSubgroupQuotientStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. If
`IsTrigonalizable G`, then:

1. for every group scheme `H` over `Spec k` and every homomorphism
   `i : H ⟶ G` with `IsClosedSubgroup i`, `IsTrigonalizable H`;
2. for every group scheme `Q` over `Spec k` with
   `[LocallyOfFiniteType Q.X.hom]` and `[IsAffineHom Q.X.hom]` and every
   homomorphism `q : G ⟶ Q` whose underlying morphism of schemes is flat and
   surjective, `IsTrigonalizable Q`.

The ingredients are existing declarations, used without change.

- `IsTrigonalizable G` (from [`Trigonalizable`](../Trigonalizable.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero coordinate vector spanning a stable line: every point of `G`, with
  values in any scheme over `Spec k`, maps it to a multiple of itself. This
  is Milne's Definition 16.1, as recorded in that module.
- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
- `Flat` and `Surjective` (Mathlib) are flatness and surjectivity of the
  underlying morphism of schemes `q.hom.hom.left : G.X.left ⟶ Q.X.left`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 16.3, p.325: "Subgroups and quotients of trigonalizable algebraic
  groups are trigonalizable."
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map
  if it is faithfully flat." and "Thus a homomorphism is a quotient map if it
  is both flat and surjective."
- Definition 1.3, p.7: "An algebraic subgroup of an algebraic group (G, m_G)
  over k is an algebraic group (H, m_H) over k such that H is a k-subscheme
  of G and the inclusion map is a homomorphism of algebraic groups."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 16.3 on
printed p.325 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.7, 99 or 325;
their p.18 entry concerns the proof of Proposition 1.40, not Proposition
1.41, and their p.324 entry concerns the first paragraph of Chapter 16, not
the affineness sentence. The 2022 errata have no entry for pp.324 or 325. Their p.7 entry adds a
sentence after Definition 1.3 (the identity of `G` factors through `H` and
gives a neutral element for `H`); it does not change the definition.

Milne's proof: "Let G be a trigonalizable algebraic group. As G admits a
faithful trigonalizable representation, so does every algebraic subgroup. Let
Q be a quotient of G. A nonzero representation of Q can be regarded as a
representation of G, and so it has a one-dimensional subrepresentation." This
is explanation only. The statement does not depend on that route.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **Subgroups.** An algebraic subgroup of `G` is a closed subscheme whose
  inclusion is a homomorphism (Definition 1.3, Proposition 1.41). It is
  presented by a homomorphism `i : H ⟶ G` that is a closed immersion. A
  closed subgroup of an affine algebraic group is affine and of finite type,
  so no hypotheses are imposed on `H`.
- **Quotients.** A quotient of `G` is the target of a quotient map, a flat
  surjective homomorphism (Definition 5.5), and it is an algebraic group,
  affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType Q.X.hom` and `IsAffineHom Q.X.hom`, and that the
  underlying morphism of `q` is flat and surjective.
- **Universes.** One universe `u` is used for the fields and the schemes.
  This is a formalization convention.
