# Algebraic subgroups of `GL_V` with a dense subgroup of unipotent elements

`Langlands.GroupScheme.GeneralLinearDenseUnipotentSubgroupStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field, `G : GroupScheme (Spec (CommRingCat.of k))`,
`n : Type` with `[Fintype n]` and `[DecidableEq n]`, and
`ρ : MatrixRepresentation G n` with `IsClosedSubgroup ρ`. Let `S` be a
subgroup of the group `Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X` of
`k`-points of `G`. Assume:

1. `S` is schematically dense in `G`: for every scheme `Z` and every closed
   immersion `z : Z ⟶ G.X.left` such that every `g ∈ S` factors as
   `s ≫ z = g.left` for some `s : Spec k ⟶ Z`, the morphism `z` is an
   isomorphism;
2. every `g ∈ S` is unipotent:
   `IsNilpotent ((ρ.rationalMatrix g : Matrix n n k) - 1)`.

The conclusion is `IsUnipotent G`.

The ingredients are existing declarations, used without change.

- `MatrixRepresentation G n` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is the type of
  homomorphisms of group schemes `G ⟶ GL_n` over `Spec k`.
- `IsClosedSubgroup ρ` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of the homomorphism `ρ` is a closed
  immersion.
- A morphism `g : Over.mk (𝟙 (Spec k)) ⟶ G.X` is a `k`-point of `G`, and
  `g.left : Spec k ⟶ G.X.left` is the underlying morphism of schemes. These
  points form a group under the multiplication of `G` (Mathlib's
  `CategoryTheory.MonObj` scoped instances), which is `G(k)`; `S` is a
  `Subgroup` of it.
- `IsClosedImmersion` and `IsIso` (Mathlib) are closed immersions and
  isomorphisms of schemes.
- `ρ.rationalMatrix g` (from
  [`MatrixRepresentationRationalPoints`](../MatrixRepresentationRationalPoints.md))
  is the invertible matrix with entries in `k` by which `g` acts in `ρ`.
  `IsNilpotent (M - 1)` says that the matrix `M` is unipotent.
- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 14.11, p.283: "An algebraic subgroup G of GL_V is unipotent if
  there exists a subgroup of G(k) that is dense in G (as a scheme) and
  consists of unipotent endomorphisms."
- Definition 1.9, p.9: "Let X be an algebraic scheme over k and S a subset of
  X(k). We say that S is schematically dense (or just dense) in X if the only
  closed subscheme Z of X such that S ⊂ Z(k) is X itself."
- Definition 1.3, p.7: "An algebraic subgroup of an algebraic group (G, m_G)
  over k is an algebraic group (H, m_H) over k such that H is a k-subscheme
  of G and the inclusion map is a homomorphism of algebraic groups."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
- 2.8, p.41: "More generally, for any vector space V over k, we define GL_V
  to be the functor R ⇝ Aut(V_R) (R-linear automorphisms). If V has finite
  dimension n, then the choice of a basis for V determines an isomorphism
  GL_V → GL_n, and GL_V is an algebraic group."
- Chapter 14 opening, p.279: "Recall that an element r of a ring is
  unipotent if r − 1 is nilpotent."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 14.11 on
printed p.283 as "An algebraic subgroup G of GL_V is unipotent if there
exists a subgroup S of G(k) that is schematically dense in G and consists of
unipotent endomorphisms", making explicit the schematic density meant in the
2017 text.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.7, 9, 41 or 135. Their p.18 entry concerns the
proof of Proposition 1.40, not Proposition 1.41.

Milne's proof: "Let S be such a subgroup. There exists a basis of V for which
S ⊂ U_n(k) (see 14.2). Then S ⊂ (U_n ∩ G)(k), and so U_n ∩ G = G. Therefore
G ⊂ U_n." Here `U_n` is the group of upper triangular unipotent matrices,
and 14.2 is Kolchin's theorem for an abstract group acting by unipotent
endomorphisms. This is explanation only. The statement does not depend on
that route.

## Derivation from the source

- **Algebraic subgroup of `GL_V`.** `V` is finite-dimensional, since `GL_V`
  is an algebraic group only then (2.8). A basis of `V`, indexed by the
  finite type `n`, identifies `GL_V` with `GL_n`. An algebraic subgroup is a
  closed subscheme (Definition 1.3, Proposition 1.41) whose inclusion is a
  homomorphism. So the data is a homomorphism `ρ : G ⟶ GL_n` that is a
  closed immersion: `IsClosedSubgroup ρ`. Such a `G` is affine and of finite
  type over `k`, so no separate finiteness hypothesis is needed. The case
  `V = 0` is included, with `n` empty.
- **Subgroup of `G(k)`.** `G(k)` is the group of `k`-points of `G`, the
  morphisms `Spec k ⟶ G` over `Spec k`, with the group law of `G`. `S` is a
  subgroup of it.
- **Dense in `G` (as a scheme).** Definition 1.9: `S` is dense in `G` when
  the only closed subscheme `Z` of `G` with `S ⊂ Z(k)` is `G` itself. In the
  statement a closed subscheme is given by a closed immersion
  `z : Z ⟶ G.X.left`, `S ⊂ Z(k)` says that every point of `S` factors
  through `z`, and "is `G` itself" says that `z` is an isomorphism.
- **Unipotent endomorphisms.** An element `g ∈ G(k)` acts on `V` through
  `G ⊂ GL_V` by the automorphism with matrix `ρ.rationalMatrix g` in the
  chosen basis. It is unipotent when this matrix minus the identity is
  nilpotent (Chapter 14 opening).
- **Unipotent group.** Milne's definition is 6.45, which is `IsUnipotent`;
  its comparison is recorded in [`Reductive.Basic`](../Reductive/Basic.md).
- **Universes.** One universe `u` is used for `k` and the schemes, including
  the closed subschemes `Z`, and the index type `n` lives in `Type`, as in
  `MatrixRepresentation`. A closed subscheme of `G` can be represented in
  universe `u`. This is a formalization convention.
