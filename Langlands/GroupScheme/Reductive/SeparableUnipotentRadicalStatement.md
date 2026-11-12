# Unipotent radicals under separable algebraic extension

`Langlands.GroupScheme.SeparableAlgebraicUnipotentRadicalStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for all fields `k K : Type u` in one universe `u`, with
`[Algebra k K]` and `[Algebra.IsSeparable k K]`, and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, writing
`bc := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))`,

```text
(∀ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
    IsUnipotentRadical i → IsUnipotentRadical (bc.map i)) ∧
  (IsPseudoReductive G ↔ IsPseudoReductive (bc.obj G)).
```

In words: let `K/k` be a separable algebraic field extension and `G` a smooth
connected affine group scheme over `k`.

1. If `i : U ⟶ G` is a `k`-unipotent radical of `G`, then its base change
   `i_K : U_K ⟶ G_K` is a `K`-unipotent radical of `G_K`.
2. `G` is pseudo-reductive over `k` if and only if `G_K` is pseudo-reductive
   over `K`.

Every ingredient is an existing declaration, used without change:

- `IsUnipotentRadical i` (from `Langlands.GroupScheme.Reductive.UnipotentRadical`)
  says that `i` is a closed immersion (`IsClosedSubgroup i`), that `U` is smooth,
  connected and unipotent, that the image subgroup functor
  `SubgroupFunctor.range i` is normal, and that this image contains the image of
  every closed subgroup of `G` over the same base with these five properties. Two
  homomorphisms satisfying it have the same image (`IsUnipotentRadical.range_eq`,
  same module). So `i` represents the ground-field unipotent radical `R_{u,k}(G)`
  of CGP Definition 1.1.1, as a closed subgroup of `G`.
- `IsPseudoReductive G` (from `Langlands.GroupScheme.Reductive.Basic`) is a
  structure with the four fields `Smooth G.X.hom`, `IsAffineHom G.X.hom`,
  `ConnectedSpace G.X.left` and `HasTrivialUnipotentRadical G`: every smooth
  connected unipotent normal closed subgroup of `G` over `k` itself has image `⊥`.
- `GroupScheme.baseChange f` (from `Langlands.AbelianScheme.GroupScheme`) is
  `(Over.pullback f).mapGrp`, the actual scheme pullback with its induced group
  law, applied to objects (`bc.obj G = G_K`) and to homomorphisms
  (`bc.map i : U_K ⟶ G_K`). Here `f` is `Spec K ⟶ Spec k`, induced by
  `algebraMap k K`.
- `Algebra.IsSeparable k K` is Mathlib's class: every element of `K` is separable
  over `k`. Separable elements are integral, so `K/k` is algebraic (Mathlib's
  instance `Algebra.IsSeparable.isAlgebraic`).

Part 1 quantifies over every representative `i`; it does not assert that one
exists. The Library's `unipotentRadicalExistence`
(`Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof`) supplies one for
every smooth connected affine group over a field. Since a `K`-unipotent radical of
`G_K` is unique up to equal image, Part 1 says that the closed subgroup
`R_{u,k}(G)_K` of `G_K` is `R_{u,K}(G_K)`.

The statement covers, for example, `K = SeparableClosure k`, every finite separable
extension and every Galois extension. It does not cover separable transcendental
extensions.

## Provenance (derived)

Source: B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second
edition (2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`
(SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`),
Proposition 1.1.9(1), printed p. 8 (PDF p. 34):

> Proposition 1.1.9 Let K/k be a separable extension of fields, and G a smooth
> connected affine k-group.
> (1) Inside of G_K we have R_{u,k}(G)_K = R_{u,K}(G_K). In particular, G is
> pseudo-reductive over k if and only if G_K is pseudo-reductive over K.

The hypotheses on `G` match: smooth, connected and affine over `k`. The two parts
of the Lean statement are the two sentences of (1). The provenance is derived for
two reasons:

1. The source allows any separable extension `K/k`, which need not be algebraic.
   This statement restricts to the separable algebraic case, the one encoded by
   Mathlib's `Algebra.IsSeparable`. The source proof treats the transcendental case
   by a separate spreading-out argument.
2. Both fields lie in one universe `u`. This is a formalization convention that
   the source does not impose.

The source's equality of subgroups of `G_K` is expressed through the Library's
predicate on representatives, as explained above: the Library has no chosen
radical object.

The forward direction of Part 2 is the already published
`PseudoReductiveSeparableExtensionStatement`
(`Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionStatement`),
proved as `pseudoReductiveSeparableExtension`. That statement has no smoothness,
affineness or connectedness hypotheses, since `IsPseudoReductive` contains them.
This statement adds the radical equality of Part 1 and the converse direction of
Part 2. The converse uses the hypotheses on `G`, because `IsPseudoReductive G`
requires them.

For the later proof (not part of this unit): the source proof, printed p. 9
(PDF p. 35), says "By Galois descent, if k′/k is a Galois extension then
R_{u,k′}(G_{k′}) descends to a smooth connected unipotent normal k-subgroup of G.
Such a descent is contained in R_{u,k}(G), so this settles the case where K/k is
Galois." For a separable algebraic `K/k`, a separable closure `L` of `K` is a
separable closure of `k`, and `L/k` and `L/K` are Galois.
