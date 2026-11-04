# A connected reductive group has a central torus with semisimple quotient

Authors: Worker 1383 (original shared draft) and Worker 1457 (source and interface verification, final exposition).

`Langlands.GroupScheme.ReductiveCentralTorusSemisimpleQuotientStatement` is a
universe-polymorphic proposition definition. This module defines the
proposition and contains no proof of it. It records the part of Milne's
Corollary 17.62 that the proof of
`ReductiveCentralTorusSurjectivityStatement` (module
`Langlands.GroupScheme.Reductive.CentralTorusSurjectivityStatement`) needs:
over any field, a connected reductive group has a closed central torus whose
quotient is semisimple.

## Quantifiers and predicates

For every universe `u`, the statement quantifies over every `k : Type u` with a
`Field k` instance and every actual group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` (a group object in
`Over (Spec k)`). Its only premise is `IsConnectedReductive G`, the published
predicate using the geometric unipotent radical (module `Langlands.GroupScheme.Reductive.Basic`):
`G` is smooth, affine and connected over `k`, and its unipotent radical is
trivial after base change to an algebraic closure of `k`. Smoothness gives
local finite presentation, and affineness gives quasi-compactness, so `G` is
of finite type over `k`, as required for Milne's algebraic groups.

The conclusion chooses a commutative group scheme `Z` over the same `Spec k`
and a homomorphism `j : Z.toGrp ⟶ G`. The first five conjuncts are the same as
in the conclusion of `ReductiveCentralTorusSurjectivityStatement`:

- `IsAffineHom Z.toGrp.X.hom` and `LocallyOfFiniteType Z.toGrp.X.hom`: the
  structure morphism of `Z` is affine and locally of finite type. Affineness
  implies quasi-compactness, so together these say that `Z` is affine of
  finite type over `k`.
- `IsTorus Z.toGrp`: the published torus predicate (module
  `Langlands.GroupScheme.Torus.Lattice`). Some field `K : Type u` with
  `Algebra k K` makes the base change of `Z` to `Spec K` isomorphic to a
  finite product of copies of the multiplicative group. Rank zero is allowed.
- `IsClosedSubgroup j`: the underlying scheme morphism of `j` is a closed
  immersion.
- `IsCentral j`: functorial centrality. Every image point over any scheme `T`
  over `Spec k`, after restriction along any `T' ⟶ T`, commutes with every
  `G`-point over `T'`.

The last conjunct concerns every actual group scheme `Q` over `Spec k` and
every homomorphism `q : G ⟶ Q` such that

- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q` holds (module
  `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`): the
  underlying morphism of `q` is flat, surjective and locally of finite
  presentation, and the range functor of the actual kernel inclusion
  `kernelι q` equals the range functor of `j` on every test scheme;
- `IsAffineHom Q.X.hom` and `LocallyOfFiniteType Q.X.hom`: `Q` is affine and
  locally of finite type over `k`.

For every such `q`, it asserts `IsSemisimple Q`, the published predicate of
module `Langlands.GroupScheme.Reductive.Semisimple`: `Q` is connected
reductive and has finite centre, that is, some actual closed subgroup represents
the full scheme-theoretic centre functor of `Q` and its structure morphism is
finite. Nilpotents of the centre are kept.

The statement does not assert that an fppf quotient by `Z` exists. It only
constrains the quotients that exist. It also does not say that `Z` is the
radical or the largest central subtorus; any closed central torus with this
property will do. No perfectness, characteristic, splitting or
algebraic-closedness hypothesis appears.

## Original source and derivation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, at
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
Printed page `p` is PDF page `p + 16`.

No single result in the source states the proposition verbatim. It is derived
from the following passages, with `Z = R(G)`, the radical.

1. Milne's reductive groups (6.46, printed p.135 / PDF p.151, recalled on
   printed p.400 / PDF p.416) are smooth connected affine algebraic groups
   whose geometric unipotent radical is trivial. This matches
   `IsConnectedReductive`. The radical `R(G)` of a connected group variety
   (6.44, printed p.135 / PDF p.151) is its largest connected solvable normal
   subgroup variety. A connected group variety is semisimple if its geometric
   radical `R(G_{k^a})` is trivial.
2. Corollary 17.62 (printed pp.372–373 / PDF pp.388–389) applies to a
   reductive group `G` over any field `k`. Part (b) gives `R(G) = Z(G)_t`, the
   largest subtorus of the centre. So `R(G)` is a torus contained in the
   centre. As an algebraic subgroup it is a closed subgroup scheme; as a torus
   (Definition 12.14, printed p.236 / PDF p.252) it is commutative, affine and
   of finite type. Its inclusion therefore satisfies the first five conjuncts,
   and Milne's centre is the functorial centre that `IsCentral` describes
   (Proposition 1.92 and the following definition, printed pp.33–34 /
   PDF pp.49–50): commutation must persist on all coefficient algebras.
   The Library expresses this on all test schemes and their refinements;
   affine tests and gluing give the same condition.
   Part (d) says that `G/R(G)` is semisimple. Neither part assumes that `k` is
   perfect.
3. By Definition 5.5 (printed p.99 / PDF p.115), a quotient map is a
   faithfully flat homomorphism. Theorem 5.13 (printed p.101 / PDF p.117)
   shows that a quotient map is determined by its kernel up to unique
   isomorphism, which defines `G/N`. Proposition 5.18 (printed p.103 /
   PDF p.119) supplies an affine algebraic quotient `G/N` when `G` is affine.
   Let `q` satisfy the hypotheses of the last conjunct. Affineness makes `Q`
   quasi-compact, so its local finite type premise makes it an algebraic group
   in Milne's sense. Flatness and surjectivity make `q` a quotient map, and
   equality of the full kernel and range functors identifies its kernel with
   `R(G)` by Yoneda. Hence 5.13 gives an isomorphism `Q ≅ G/R(G)`.
   The hypotheses on `Q` lose no canonical quotient: 5.18 supplies one that
   is affine and of finite type. Its quotient map is faithfully flat, and
   homomorphisms of finite-type schemes over a field are locally of finite
   presentation, so it also has the required fppf property. Quotient
   uniqueness transfers the same conclusion to every `Q` under consideration.
4. Milne's semisimple groups are reductive, because the unipotent radical is
   contained in the radical. Proposition 19.10 (printed p.400 / PDF p.416)
   says that a reductive group is semisimple if and only if its centre is
   finite. Hence `G/R(G)` is connected reductive with finite centre, which is
   the definition of `IsSemisimple` used in this Library. The module
   `Langlands.GroupScheme.Reductive.Semisimple` cites 19.10 for this
   definition. Semisimplicity passes to the isomorphic `Q` by
   `IsSemisimple.of_iso` from that module.

## Errata

The official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`,
SHA256 `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`, at
`/home/taskhub/pilot/literature/J. S. Milne - Errata for Algebraic Groups (2017), HTML snapshot 2026-11-02.html`,
has no entry for 1.92, 5.5, 5.13, 5.18, 6.44, 6.46, 12.14, 17.62(b),(d) or 19.10.
Its Chapter 5 entry concerns only Exercise 5-7, and its Chapter 19 entry only
Definitions 19.7 and 19.8. Its entry for 12.41 concerns a step used only in the
proof of 17.62(e), which this derivation does not use.

## Use in the Library

The intended proof of `ReductiveCentralTorusSurjectivityStatement`
(task `5c7bdf70-6574-45e3-88a3-ad60aba3e6d9`) takes the torus `j` from this
statement and forms an affine fppf quotient `q : G ⟶ Q` by its range. This
statement makes `Q` semisimple. `SemisimplePerfectStatement` (Milne 21.50)
then makes `Q` perfect, and the derived subgroup of `G` maps onto `Q`.

## Proof boundary

Defining and compiling this proposition proves nothing. A proof has to
construct an actual closed central torus of a connected reductive group over an
arbitrary field, for example the largest central subtorus, and show that every
affine fppf quotient by it is connected reductive with finite scheme-theoretic
centre. The predicate `IsLargestCentralSubtorus` (module
`Langlands.GroupScheme.Rational.LeviSubgroup`) characterizes a supplied
largest central subtorus; that predicate alone gives no existence result.
The proof of this proposition is a separate obligation.
