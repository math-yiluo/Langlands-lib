# Statement: split unipotent groups are affine spaces

Worker 75.

`Langlands.GroupScheme.SplitUnipotentAffineSpaceStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.HasSplitSeries` and, through its imports, the group-scheme vocabulary.
- Mathlib's `Mathlib.AlgebraicGeometry.AffineSpace`, for the affine space `𝔸(ι; S)`.

## Lean statement

```lean
def SplitUnipotentAffineSpaceStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom H.X.hom → RelativeRoot.HasSplitSeries n H →
      Nonempty (H.X ≅ Over.mk (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)))
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `H : GroupScheme S`, `H.X` is its
  scheme over `S`, an object of `Over S`; `H.X.hom` is its structure morphism.
- `IsAffineHom H.X.hom`: Mathlib's affine morphisms. Over `Spec k` this says that `H` is an
  affine scheme.
- `RelativeRoot.HasSplitSeries n H` (module `Rational.RootSubgroupStructureStatement`),
  defined by recursion on `n`:
  - for `n = 0`, `H` is trivial: its subgroup functor of points is `⊥` on every test scheme;
  - for `n + 1`, there are group schemes `K` and `V` over `Spec k`, a closed subgroup
    `j : K ⟶ H` with `K` smooth and connected and normal image, and a homomorphism
    `q : H ⟶ V` that is a represented fppf quotient with kernel exactly the image of `j`
    (`RelativeRoot.IsFppfQuotient`), such that `V` is a one-dimensional vector group (its
    points on every `k`-scheme `T` are naturally the additive group `Γ(T, ⊤)`, that is,
    `V ≅ 𝔾_a`) and `HasSplitSeries n K`.
- `𝔸(ULift.{u} (Fin n); Spec k)`: Mathlib's affine space over `Spec k` with `n` coordinates,
  the spectrum of the polynomial ring in `n` variables. The index type `Fin n` is lifted to
  universe `u` because Mathlib's affine space requires the index type and the base scheme to
  share a universe.
- `Over.mk (𝔸(…) ↘ Spec k)`: this affine space as an object of `Over (Spec k)`, through its
  structure morphism.

## Statement and quantifiers

For every field `k : Type u`, every natural number `n` and every group scheme `H` over
`Spec k`: if `H` is affine over `k` and admits a series of length `n` as above, then there is
an isomorphism in `Over (Spec k)` between `H.X` and the affine space `𝔸ⁿ_k`. That is, the
underlying scheme of `H` is isomorphic to `𝔸ⁿ_k` by an isomorphism of `k`-schemes. The
isomorphism need not respect the group structure, and none is chosen.

The case `n = 0` says that the trivial group is `Spec k = 𝔸⁰_k`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- 14.66, p.299: "Let G be a split unipotent algebraic group of dimension n. Then the
  underlying scheme of U is isomorphic to Aⁿ. Indeed, inductively, G is a G_a-torsor over
  Aⁿ⁻¹ (2.68), and such a torsor is trivial (2.72)." The letter `U` in the second sentence is
  a misprint for `G`.
- Definition 14.61, p.299: "A unipotent algebraic group G over k is split if it admits a
  subnormal series each of whose quotients is isomorphic to G_a." (A special case of
  Definition 6.33, p.132.)
- 14.62, p.299: "A split unipotent algebraic group is automatically smooth and connected."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine over a base field k."

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) has a single entry under Chapter 14, about
Theorem 13.47(c) on p.273. It has no correction to 14.61, 14.62, 14.66 or the Chapter 14
convention.

Milne's proof, quoted above, is explanation only; the statement does not depend on it.

## Derivation from the source

- **Algebraic groups are affine.** By the Chapter 14 convention a split unipotent algebraic
  group is affine. The statement therefore assumes `IsAffineHom H.X.hom`.
- **Split series.** Definition 14.61 asks for a subnormal series
  `H = H₀ ⊃ H₁ ⊃ ⋯ ⊃ H_m = e` of algebraic subgroups with `Hᵢ/Hᵢ₊₁ ≅ 𝔾_a`. Read from the
  top, this is the recursion in `HasSplitSeries`: `K = H₁` is a closed normal subgroup, the
  quotient map `q : H → V` has kernel `K`, `V ≅ 𝔾_a`, and `K` carries the rest of the series.
  `HasSplitSeries` also records that each `K` is smooth and connected. This holds for Milne's
  series by 14.62, since each `Hᵢ` is itself split. Milne also assumes `H` unipotent; a group
  with such a series is unipotent, since extensions of unipotent groups are unipotent.
- **Dimension `n`.** Each quotient `𝔾_a` has dimension 1, so the length of a split series is
  `dim H`. Conversely, for a split unipotent `H` of dimension `n`, every split series has
  length `n`. The Library proves `HasSplitSeries.smoothOfRelativeDimension` (module
  [`Rational.SplitSeriesDimension`](../Rational/SplitSeriesDimension.md)): for affine connected
  `H`, a series of length `n` makes `H` smooth of relative dimension `n`. The statement
  therefore quantifies over `n` and a series of length `n`.
- **Underlying scheme.** "The underlying scheme of G is isomorphic to Aⁿ" is read over `k`, as
  everything in the book is a `k`-scheme: the conclusion is an isomorphism in `Over (Spec k)`.

## Scope

- Only 14.66 is stated. Definitions 14.61 and 6.33 are those of the Library's
  `HasSplitSeries` and `IsSplitUnipotent`, not new definitions here.
- The torsor description in Milne's proof (2.68, 2.72) is not stated.

## Related Library results

- [`Unipotent.PerfectFieldSplitStatement`](PerfectFieldSplitStatement.md) states (and the
  Library proves) that a smooth connected affine unipotent group over a perfect field is
  split unipotent (Milne 16.24; see also 14.63). With the present statement it shows that such
  a group is isomorphic as a `k`-scheme to an affine space, which is the input to Milne's
  proof of Theorem 17.93(a).
- [`SplitUnipotentAffineTorsorStatement`](../SplitUnipotentAffineTorsorStatement.md) states
  (and the Library proves) that a torsor under a smooth affine split unipotent group over an
  affine `k`-scheme has a section. This is the triviality of torsors used in Milne's proof.
