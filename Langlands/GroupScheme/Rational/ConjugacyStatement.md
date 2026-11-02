# Conjugacy of maximal split tori and the split rank

Author: Worker 1220.

This module states, as a `Prop`-valued definition, the conjugacy theorem for
maximal split tori of a connected reductive group over a field, together with
the identification of the split rank with the dimension of any maximal split
torus. Nothing is proved here. The declaration is in the namespace
`Langlands.GroupScheme`.

## Sources

- Borel and Tits, *Groupes réductifs* (1965), source ID
  `borel-tits-1965-groupes-reductifs`, SHA-256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
  Printed page = PDF page + 53.
  - 4.21 (printed p.93, PDF p.40): « Les tores déployés sur k maximaux de G
    sont conjugués sur k. »
  - 4.23 (printed p.93, PDF p.40): « La dimension (commune vu 4.21) des tores
    déployés sur k maximaux de G est le k-rang de G et est notée r_k(G). »
- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - Theorem 25.10 (printed p.546, PDF p.562): "Any two maximal split tori in G
    are conjugate by an element of G(k)."

In both sources `G` is a connected reductive group over the field `k`.

## The statement

`MaximalSplitTorusConjugacyStatement : Prop` says: for every field
`k : Type u`, with `S = Spec (CommRingCat.of k)`, and every
`G : GroupScheme S` with the published `IsConnectedReductive G`
(module `Langlands.GroupScheme.Reductive.Basic`), both of the following hold.

1. **Conjugacy.** For all commutative group schemes `T`, `T'` over `S` and
   all homomorphisms `i : T.toGrp ⟶ G`, `i' : T'.toGrp ⟶ G` with
   `IsMaximalSplitTorus i` and `IsMaximalSplitTorus i'`, there are a rational
   point `g : Over.mk (𝟙 S) ⟶ G.X` (a point of `G(k)`) and an isomorphism
   `e : T.toGrp ≅ T'.toGrp` of group schemes with
   `i ≫ (G.innerIso g).hom = e.hom ≫ i'`.
2. **Rank.** For every commutative `T` and `i : T.toGrp ⟶ G` with
   `IsMaximalSplitTorus i`, every finite `I : Type u` and every isomorphism
   `T.toGrp ≅ splitTorus S I`, one has `(Nat.card I : ℕ∞) = splitRank G`.

The predicates `IsMaximalSplitTorus` and `splitRank` are those of the module
`Langlands.GroupScheme.Rational.SplitTorus`: a maximal split torus is a closed
immersion of a split torus that does not factor through a strictly larger
split subtorus, and `splitRank G` is the supremum of `Nat.card I` over closed
homomorphisms `splitTorus S I ⟶ G`. `G.innerIso g` (module
`Langlands.GroupScheme.InnerAutomorphism`) is the inner automorphism of `G`
that conjugates every `T`-valued point by the image of `g`. `splitTorus S I`
(module `Langlands.GroupScheme.Torus.Split`) is `𝔾ₘ^I`, and it requires
`Finite I`.

## Correspondence with the sources

- **Conjugacy.** The sources speak of subgroups `S, S'` and an element
  `g ∈ G(k)` with `g S g⁻¹ = S'`. Here a split torus is a closed-immersion
  homomorphism. Conjugating the image of `i` by `g` gives the image of `i'`
  exactly when `i ≫ int(g)` and `i'` agree up to an isomorphism of their
  sources, which is the equation `i ≫ (G.innerIso g).hom = e.hom ≫ i'`.
  Conjugation by `g` is applied after `i`; whether `g` or `g⁻¹` is the
  conjugating element in the sources does not matter, since `G(k)` is a group.
- **Rank.** Borel–Tits 4.23 *defines* the `k`-rank as the common dimension of
  the maximal split tori, using 4.21. The module `SplitTorus` instead defines
  `splitRank G` as a supremum over all closed split subtori. Part 2 asserts
  that the two definitions agree for connected reductive `G`: the rank of the
  split torus `𝔾ₘ^I`, its number `Nat.card I` of factors, equals the supremum.
  This identification is a derived reformulation of 4.23 combined with 4.21.
  Since `splitTorus S I` requires `Finite I`, the quantifier over `I` ranges
  over finite types, and `Nat.card I` is the actual cardinality.

The statement is a reformulation of these source theorems in the conventions
above. It is the first of the statements of the task; the relative root
system, rational Bruhat, generic-centralizer and `GL_n` statements are planned
for later modules and are not part of this one.
