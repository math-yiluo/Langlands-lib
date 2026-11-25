# Solvable radicals under separable algebraic extension

`Langlands.GroupScheme.SeparableAlgebraicSolvableRadicalStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for all fields `k K : Type u` in one universe `u`, with
`[Algebra k K]` and `[Algebra.IsSeparable k K]`, and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, writing
`bc := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))`,

```text
∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G),
  IsSolvableRadical r → IsSolvableRadical (bc.map r).
```

In words: let `K/k` be a separable algebraic field extension and `G` a smooth
connected affine group scheme over `k`. If `r : R ⟶ G` is a solvable radical of
`G` over `k`, then its base change `r_K : R_K ⟶ G_K` is a solvable radical of
`G_K` over `K`.

Every ingredient is an existing declaration, used without change:

- `IsSolvableRadical r` (from `Langlands.GroupScheme.Rational.LeviSubgroup`) is a
  structure with the fields: `r` is a closed immersion (`IsClosedSubgroup r`);
  `R` is smooth, connected and solvable (`IsSolvableGroupScheme R`); the image
  subgroup functor `SubgroupFunctor.range r` is normal; and this image contains
  the image of every closed subgroup of `G` over the same base with these four
  properties. So `r` represents the radical `R(G)` of Milne 6.44, the largest
  smooth connected solvable normal algebraic subgroup of `G`, as a closed
  subgroup of `G`.
- `IsSolvableGroupScheme H` (from `Langlands.GroupScheme.Absolute.Borel`) says
  that the abstract group of points of the base change of `H` to the algebraic
  closure of its base field, over that algebraic closure, is solvable. For smooth
  affine groups this agrees with Milne's Definition 6.26 of solvability, by Milne
  6.31, 6.30, 6.20(b) and 6.21, as explained in `Absolute/Borel.md`. That
  equivalence is not formalized. All groups tested here are smooth.
- `GroupScheme.baseChange f` (from `Langlands.AbelianScheme.GroupScheme`) is
  `(Over.pullback f).mapGrp`, the actual scheme pullback with its induced group
  law, applied here to homomorphisms (`bc.map r : R_K ⟶ G_K`). Here `f` is
  `Spec K ⟶ Spec k`, induced by `algebraMap k K`.
- `Algebra.IsSeparable k K` is Mathlib's class: every element of `K` is separable
  over `k`. Separable elements are integral, so `K/k` is algebraic (Mathlib's
  instance `Algebra.IsSeparable.isAlgebraic`).

The statement quantifies over every representative `r`; it does not assert that
one exists. The Library theorem `solvableRadicalExistence`
(`Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof`) supplies one for
every smooth connected affine group over a field. Two representatives have the
same image, since each image contains the other. So the statement says that the
closed subgroup `R(G)_K` of `G_K` is `R(G_K)`.

The statement covers, for example, `K = SeparableClosure k`, every finite
separable extension and every Galois extension. It does not cover separable
transcendental extensions or inseparable extensions.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`),
Proposition 19.1, printed p. 397 (PDF p. 413):

> PROPOSITION 19.1. The formation of R(G) commutes with separable algebraic
> field extensions.

Here `G` is the connected group variety of the preceding paragraph: "Let G be a
connected group variety over k. Recall (6.44) that, among the connected normal
solvable subgroup varieties of G there is a largest one, containing all others.
This is the radical R(G) of G." A group variety is a smooth algebraic group
(1.26, printed p. 13). From printed p. 162 (PDF p. 178) on, Milne says: "By
'algebraic group' we shall mean 'affine algebraic group' and by 'group variety'
we shall mean 'affine group variety'." The `IsAffineHom G.X.hom` hypothesis
records this convention, which applies to Chapter 19. The definition of the
radical is 6.44, printed p. 135 (PDF p. 151), in Section 6h, whose introduction
says "Throughout this section, all algebraic groups are affine."

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists
Chapter 19 corrections only on p. 399 (Definitions 19.7 and 19.8) and Chapter 6
corrections only on p. 136 (Example 6.48). None concerns 19.1 or 6.44.

The provenance is derived for three reasons:

1. Milne's equality of algebraic subgroups `R(G)_K = R(G_K)` of `G_K` is
   expressed through the Library's predicate on representatives, as explained
   above: the Library has no chosen radical object.
2. Solvability is the Library's `IsSolvableGroupScheme`, explained above.
3. Both fields lie in one universe `u`. This is a formalization convention that
   the source does not impose.

## For the proof (not part of this module)

The Library proves the proposition as `separableAlgebraicSolvableRadical` in
[`Rational.SeparableSolvableRadicalProof`](SeparableSolvableRadicalProof.md).

Milne's proof, printed p. 397: "Let k′/k be a finite separable extension. As
R(G)_{k′} is connected, normal, and solvable it is contained in R(G_{k′}). It
suffices to prove they are equal when k′ is Galois over k. By uniqueness,
R(G_{k′}) is stable under the action of Gal(k′/k) on G_{k′}, and therefore arises
from a subgroup variety H of G (see 1.54). Now R(G)_{k′} ⊆ R(G_{k′}) = H_{k′},
and so R(G) ⊆ H. But H is connected, normal, and solvable (1.36, 6.31), and so
R(G) = H by maximality."

The printed proof treats finite separable extensions. The same argument applies
to every Galois extension, since 1.54(b), printed p. 22 (PDF p. 38), allows
infinite Galois extensions: "Let k′ be a Galois extension of k (possibly
infinite) and let Γ = Gal(k′/k). Then H′ is defined over k if and only if it is
stable under the action of Γ on G′". For a separable algebraic `K/k`, let `L` be
a separable closure of `K`. Then `L` is a separable closure of `k`, so `L/k` and
`L/K` are Galois. The Galois case gives `R(G)_L = R(G_L)` and
`R(G_K)_L = R(G_L)`. Hence `R(G)_K` and `R(G_K)` have the same base change to
`L`, and they are equal by the uniqueness in 1.54(a), printed p. 21 (PDF p. 37).

The published `SeparableAlgebraicUnipotentRadicalStatement`
(`Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalStatement`) is the
analogous statement for unipotent radicals, and
`IsUnipotentRadical.galoisRadicalDescent`
(`Langlands.GroupScheme.Reductive.GaloisRadicalDescent`) carries out the Galois
descent step for unipotent radicals.
