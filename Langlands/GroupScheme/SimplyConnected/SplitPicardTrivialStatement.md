# Split semisimple groups: simple connectedness and trivial Picard group

`Langlands.GroupScheme.SplitSemisimpleSimplyConnectedPicardStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for every field `k : Type u` and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with

```text
IsSemisimple G → HasSplitMaximalTorus G →
  (IsSimplyConnected G ↔
    ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
      Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial G.X.left)).
```

In words: a semisimple group over a field that has a split maximal torus is
simply connected exactly when every line bundle on its underlying scheme is
trivial, that is, when `Pic(G) = 0`.

Every ingredient is an existing declaration, used without change:

- `IsSemisimple G` (from
  [`Reductive.Semisimple`](../Reductive/Semisimple.md)) says that `G` is
  connected reductive (`IsConnectedReductive`: smooth, affine, connected, and
  the unipotent radical of the base change to an algebraic closure is
  trivial) and that its scheme-theoretic centre is finite.
- `HasSplitMaximalTorus G` (from
  [`Torus.FiniteGaloisSplitMaximal`](../Torus/FiniteGaloisSplitMaximal.md))
  says that there are a commutative group scheme `T` and a homomorphism
  `i : T.toGrp ⟶ G` with `IsSplitTorus T.toGrp` and `IsMaximalTorus i`.
  `IsSplitTorus` ([`Torus.Split`](../Torus/Split.md)) means isomorphic to the
  split torus `𝔾_m^I` for a finite index type `I`. `IsMaximalTorus i`
  ([`Torus.Maximal`](../Torus/Maximal.md)) means that `T` is a torus, `i` is a
  closed subgroup, and `i` factors through no larger closed torus of `G`.
- `IsSimplyConnected G` (from [`SimplyConnected.Basic`](Basic.md)) says that
  `G` is semisimple and that every central isogeny `f : H ⟶ G` from a
  semisimple group `H` over `k` is an isomorphism. Central isogenies
  (`IsCentralIsogeny`, from
  [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md)) are finite, flat,
  surjective and locally of finite presentation, with central kernel.
- `Langlands.AlgebraicGeometry.Picard.LineBundle X` (from
  [`Picard.LineBundle`](../../AlgebraicGeometry/Picard/LineBundle.md)) is the
  full subcategory of sheaves of `𝒪_X`-modules that are locally free of rank
  one. `LineBundle.trivial X` is the structure sheaf `𝒪_X`. An isomorphism in
  `LineBundle X` is an isomorphism of the underlying module sheaves. The
  isomorphism classes of line bundles form the Picard group, whose identity
  element is the class of `𝒪_X`. So the right-hand side says exactly that
  `Pic(G) = 0`; the group structure itself is not used. The same encoding is
  used by the published `LinearPicardTrivialStatement` and
  `SplitTorusBorelIsomorphismStatement`.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The two directions are two separate results of Milne's Chapter 18:

- Proposition 18.19, printed p. 391 (PDF p. 407): "Let G be a split
  connected group variety. If X(G) = 0 and Pic(G) = 0, then G is simply
  connected."
- Corollary 18.24, printed p. 393 (PDF p. 409): "If G is simply connected,
  then Pic(G) = 0." It lies in Section 18d, whose standing assumption
  (printed p. 392, PDF p. 408) is: "Throughout this section, G is a split
  connected group variety and B is a Borel subgroup of G that is split as a
  solvable algebraic group."

The surrounding conventions are:

- Chapter 18 opens, printed p. 387 (PDF p. 403), with "Recall that all
  algebraic groups are affine over a base field k." The Library's
  `IsSemisimple` includes affineness (`IsConnectedReductive.isAffineHom`), so
  nothing is lost here.
- Section 18c, printed p. 389 (PDF p. 405): "In this section, G is a connected
  group variety over k and X(G) = Hom(G, Gm)." In 18.9 on the same page, the
  isomorphism classes of line bundles on a variety form "the Picard group
  Pic(X) of X (see A.77)". A.77, printed p. 584 (PDF p. 600), defines an
  invertible sheaf as "a locally free O_X-module of rank 1".
- Definition 18.5, printed p. 388 (PDF p. 404): "A connected group variety G
  is simply connected if every multiplicative isogeny G′ → G of connected group
  varieties is an isomorphism."
- Definition 17.101, printed p. 384 (PDF p. 400): "A group variety over k is
  split if it has a Borel subgroup that is split (as a solvable group)."
  Section 18c recalls this on printed p. 390 (PDF p. 406): "We now assume
  that G is split. Recall (17.101) that this means that G contains a Borel
  subgroup B that is split as a solvable algebraic group".

The Lean statement is derived from these results by the following
identifications, each taken from Milne:

1. **Semisimple groups.** The Library's `IsSemisimple` is connected reductive
   with finite centre. Milne, printed p. 400 (PDF p. 416), recalls: "Recall
   (6.46) that an algebraic group G over a field k is said to be reductive if
   it is smooth and connected and the unipotent radical of Gka is trivial."
   Proposition 19.10 on the same page says that for a reductive group, "(a) G
   is semisimple" and "(c) Z(G) is finite" are equivalent. So `IsSemisimple G`
   is Milne's semisimple group, and `G` is a connected group variety.
2. **Split.** For reductive groups Milne's notion of split is equivalent to
   having a split maximal torus. Remark 17.104, printed p. 384 (PDF p. 400):
   "We shall see that a reductive algebraic group over k is split if and only
   if it has a split maximal torus (21.64)." Definition 19.22, printed p. 402
   (PDF p. 418): "A reductive group is splittable if it contains a split
   maximal torus." Proposition 21.64, printed p. 443 (PDF p. 459): "A reductive
   group G is splittable (19.22) if and only if it is split as a group variety
   (17.101)." The Library's `HasSplitMaximalTorus` is the splittable
   condition of 19.22, as its docstring records.
3. **Simply connected.** Proposition 19.15, printed p. 400 (PDF p. 416): "A
   semisimple group G is simply connected if and only if every central
   isogeny G′ → G from a semisimple group G′ to G is an isomorphism." Its
   proof, printed p. 401 (PDF p. 417), begins: "When G is semisimple, to say
   that an isogeny G′ → G is central with G′ semisimple is the same as saying
   that it is multiplicative with G′ a connected group variety." So for
   semisimple `G`, Milne's Definition 18.5 is the Library's
   `IsSimplyConnected`; `SimplyConnected/Basic.md` and
   `CentralIsogeny/Basic.md` record the comparison of definitions.
4. **No characters.** Proposition 18.19 needs `X(G) = 0`. For semisimple `G`
   this always holds. Corollary 21.50, printed p. 440 (PDF p. 456): "Every
   semisimple algebraic group is perfect", that is, `G = DG`. Corollary 6.19,
   printed p. 129 (PDF p. 145), assumes "that G is affine or smooth", and its
   part (d) reads: "Let H be a commutative algebraic group over k and R a
   k-algebra. Every homomorphism GR → HR is trivial on (DG)R." With
   `H = 𝔾_m` and `R = k`, every character of `G` is trivial.

Combining: for semisimple `G` with a split maximal torus, `G` is a split
connected group variety with `X(G) = 0`. If every line bundle is trivial, then
18.19 makes `G` simply connected in Milne's sense, hence `IsSimplyConnected G`
by 19.15. Conversely, `IsSimplyConnected G` gives Milne's simple
connectedness by 19.15, and 18.24 gives `Pic(G) = 0`.

The provenance is derived for these reasons:

- Milne states the two directions separately, for split connected group
  varieties, with the extra hypothesis `X(G) = 0` only in 18.19. The Lean
  statement specializes both to semisimple groups and joins them into one
  equivalence. The restriction to semisimple groups is forced by the Library's
  `IsSimplyConnected`, which includes `IsSemisimple`.
- Milne's split hypothesis is replaced by the equivalent (for reductive
  groups) `HasSplitMaximalTorus`. Milne proves 18.19 and 18.24 only for split
  groups, and the statement keeps this hypothesis.
- `Pic(G) = 0` is stated as: every line bundle is isomorphic to the trivial
  one.
- `k` lies in an arbitrary universe `u`. This is a formalization convention.

Errata. The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 17, corrections only on pp. 360, 364 and 386 (Exercise 17-7); for
Chapter 18, only the last sentence of 18.4 and Exercise 18-1 (pp. 388 and
396, "G should be reductive") and the target of α in 18.8 (p. 389); for
Chapter 19, only Definition 19.7 (p. 399); for Chapter 21, on p. 440 only
that "The proof of Theorem 21.51 has been rewritten", and further entries on
pp. 445 and later. For Chapter 6 it displays only a p. 136 entry (Example
6.48). The HTML source of the snapshot also contains, inside a comment that
is not displayed, the note "*p.129, 6.19. In (c,d,e), G should be assumed to
be smooth (to be safe)." Semisimple groups are smooth, so 6.19(d) applies in
either reading. Its Appendix A corrections are only on pp. 570 and 582. None
concerns 17.101, 17.104, 18.5, 18.19, 18.22, 18.24, 19.10, 19.15, 19.22,
21.50, 21.64 or A.77.

## For a proof (not part of this module)

Milne's route can be followed. The Library proves the statement as
`splitSemisimpleSimplyConnectedPicard` in `SplitPicardReduction`, by applying
`splitSemisimplePicardReduction` to the two geometric inputs
`splitCentralIsogenyPicardCharacterLifting` and
`splitSemisimplePicardTrivialCover`.

- **If.** Milne's proof of 18.19 (printed p. 392, PDF p. 408) reads: "Let
  φ: G′ → G be a multiplicative isogeny of connected group varieties. In the
  exact sequence in (129) X(G) → X(G′) → X(Ker φ) → Pic(G), the groups X(G)
  and Pic(G) are zero, the group X(Ker φ) is finite, and the group X(G′) is
  torsion-free (because G′ is smooth and connected). Therefore X(Ker φ) = 0,
  which implies that Ker(φ) = e." The sequence (129) is Proposition 18.18,
  printed p. 391 (PDF p. 407), for a surjective homomorphism of split
  connected group varieties with kernel of multiplicative type. It is deduced
  by the snake lemma from Theorem 18.15, the exact sequence
  `0 → X(G) → X(T) → Pic(G/B) → Pic(G) → 0` of printed p. 390 (PDF p. 406),
  whose proof Milne defers to the last section of Chapter 18. The final
  implication uses that `Ker φ` is determined by its group of characters over
  `k`. This holds for diagonalizable groups, for example subgroups of a split
  torus.
- **Only if.** Milne's proof of 18.24 (printed p. 393, PDF p. 409) reads: "If
  G is simply connected, then the isogeny in Proposition 18.22 is an
  isomorphism, and so Pic(G) ≃ Pic(G̃) = 0." Proposition 18.22 (Iversen 1976,
  2.7), printed p. 392 (PDF p. 408), constructs "a multiplicative isogeny
  G̃ → G with G̃ a connected group variety such that Pic(G̃) = 0". By Lemma
  19.14, printed p. 400 (PDF p. 416), `G̃` is again semisimple, and "A
  multiplicative isogeny is central by rigidity (12.38)" (printed p. 387,
  PDF p. 403). So the Library form of simple connectedness applies to this
  isogeny.
