# Statement: a maximal split torus meets every real component of a reductive group

Lean module: `Langlands.GroupScheme.Rational.RealReductiveSplitTorusComponentsStatement`,
namespace `Langlands.GroupScheme`. The module defines one proposition and proves nothing.

```lean
def RealReductiveSplitTorusComponentsStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ g : RingPoint ℝ G.X ℝ, ∃ s : RingPoint ℝ S.X ℝ,
        ConnectedComponents.mk (α := RingPoint ℝ G.X ℝ) (s ≫ i.hom.hom) =
          ConnectedComponents.mk g
```

## Meaning

Let `G` be a connected reductive group scheme over `ℝ` (`IsConnectedReductive G`) and let
`i : S → G` be a maximal split torus (`IsMaximalSplitTorus i`: `S` is a split torus, `i` is a
closed subgroup inclusion, and no strictly larger split subtorus contains it). Give the real
points `G(ℝ) = RingPoint ℝ G.X ℝ` the evaluation topology of
`Langlands.AlgebraicGeometry.PointTopology.AffineScheme`. That is the usual real topology:
the coarsest topology making every regular function continuous. The proposition says that
every real point `g` lies in the same connected component of `G(ℝ)` as the image
`s ≫ i.hom.hom` of some real point `s` of `S`. Equivalently, `G(ℝ) = G(ℝ)⁰ · i(S(ℝ))`, where
`G(ℝ)⁰` is the identity component, so the map from `S(ℝ)` to the set of components of `G(ℝ)` is
surjective.

The binder `[IsAffine G.X.left]` is needed only to form the evaluation topology. It follows
from `IsConnectedReductive G`. No topology on `S(ℝ)` is used.

## Source

Armand Borel and Jacques Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), registered as
`borel-tits-1965-groupes-reductifs` (SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`), Theorem 14.4 (Matsumoto),
printed p. 146 (PDF page 93):

> 14.4. Théorème (Matsumoto). — Supposons G connexe, défini sur R, et soit S un tore déployé
> sur R maximal de G. Alors G_R = (G_R)^0 . S_R.

The proof continues on printed p. 147 (PDF page 94). Correspondence with the Lean statement:

- The source allows any connected `G` defined over `ℝ`. The Lean statement keeps only
  connected reductive `G`, which is the case the source's proof reduces to (via a Levi
  decomposition) in its first paragraph.
- "Tore déployé sur R maximal" is the Library's `IsMaximalSplitTorus i`.
- In the source, `(G_R)^0` is the neutral component in the sense of 14.1, where `π₀` means
  path components, and `G_R` carries the usual topology of 9.1. The usual topology is the
  Library's evaluation topology. Every path component lies in a connected component, so the
  source's `G_R = (G_R)^0 · S_R` implies the Lean statement. (For these smooth groups `G(ℝ)` is
  a manifold, and the two notions of component agree.)
- `G_R = (G_R)^0 · S_R` says each point is `c · s` with `c` in the neutral component and `s` in
  `S_R`. Right translation by `s` is a homeomorphism, so `c · s` lies in the component of `s`.
  The Lean statement records exactly this: every component contains a point of `S_R`.

Corollary 14.5 (`π₀(G_R)` is a quotient of `(ℤ/2ℤ)^r`, where `r` is the real rank) is not
stated here.

## Relation to the Library

The proof is in `Langlands.GroupScheme.Rational.RealReductiveSplitTorusComponentsProof`
(`Langlands.GroupScheme.realReductiveSplitTorusComponents`).

It is meant as an input for the first conjunct of
`Langlands.GroupScheme.RealPointComponentsStatement` (module
`Langlands.GroupScheme.Rational.RealPointComponentsStatement`): the real points of a simply
connected semisimple group are connected. The same component
conclusion for all smooth connected affine real groups is
`Langlands.GroupScheme.RealMaximalSplitTorusComponentsStatement`, proved as
`realMaximalSplitTorusComponents`
([`RealMaximalSplitTorusComponentsProof`](RealMaximalSplitTorusComponentsProof.md)) by a
reduction to the present proposition; its non-reductive case uses a Levi decomposition
(`characteristicZeroLeviDecomposition`). The present proposition is the reductive
case.
