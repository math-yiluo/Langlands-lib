# Real approximation over the rationals

`Langlands.GroupScheme.RealApproximationStatement` is a Prop-valued
definition with no universe parameters. This module defines the proposition
and proves nothing.

## Statement

The proposition says: let `G : GroupScheme (Spec (CommRingCat.of ℚ))` be a
group scheme over `ℚ` with `[IsAffine G.X.left]`, `Smooth G.X.hom` and
`ConnectedSpace G.X.left`. Then

```text
DenseRange (fun p : RingPoint ℚ G.X ℚ => p.changeRing (Algebra.ofId ℚ ℝ))
```

In words: for a connected group variety `G` over `ℚ`, the image of the group
`G(ℚ)` of rational points in the group `G(ℝ)` of real points is dense for the
real topology.

The ingredients are existing declarations, used without change.

- `GroupScheme S` (from `Langlands.AbelianScheme.GroupScheme`) is
  `Grp (Over S)`, a group object in schemes over `S`. `G.X : Over S` is its
  underlying scheme over `S`, `G.X.hom` its structure morphism and
  `G.X.left` the underlying scheme.
- `RingPoint ℚ G.X A` (from
  [`PointTopology.ProductRingPoints`](../../AlgebraicGeometry/PointTopology/ProductRingPoints.md))
  is the set of actual morphisms `Spec A ⟶ G.X` over `Spec ℚ`, for a
  `ℚ`-algebra `A`: the `A`-points `G(A)`. Here `A = ℚ` and `A = ℝ`.
- `RingPoint.changeRing (Algebra.ofId ℚ ℝ)` (same module) precomposes a
  rational point with `Spec ℝ ⟶ Spec ℚ`. It is the map `G(ℚ) → G(ℝ)`
  induced by the inclusion `ℚ → ℝ`.
- The topology on `RingPoint ℚ G.X ℝ` is the instance of
  [`PointTopology.AffineScheme`](../../AlgebraicGeometry/PointTopology/AffineScheme.md),
  which needs `[IsAffine G.X.left]`. It is induced from the evaluation
  topology on `ℚ`-algebra maps `Γ(G.X.left) → ℝ`: the coarsest topology for
  which every evaluation `p ↦ p(a)`, for `a` a global function, is
  continuous into `ℝ`. This is the real topology of Milne's statement. If
  `x₁, …, xₙ` generate the coordinate ring over `ℚ`, every evaluation is a
  polynomial with rational coefficients in the evaluations at the `xᵢ`. So
  the evaluation topology is the subspace topology of the image of
  `p ↦ (p(x₁), …, p(xₙ))` in `ℝⁿ`. Real points of `G` over `ℚ` are the same
  as real points of the base change `G_ℝ` over `ℝ`.
- `Smooth G.X.hom` and `ConnectedSpace G.X.left` are from Mathlib: the
  structure morphism is smooth and the underlying topological space is
  connected. A smooth morphism is locally of finite presentation, and an
  affine scheme is quasi-compact, so `G` is of finite type over `ℚ`.
- `DenseRange f` (Mathlib) says that the range of `f` is dense.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Theorem 25.70 (Real approximation), printed p. 564: "For
every connected group variety G over Q, the group G(Q) is dense in G(R)."

The context and definitions:

- Conventions, printed p. 4: "After p. 162, all algebraic groups are
  affine." Chapter 25 opening, printed p. 544: "Recall that all algebraic
  groups are affine over a base field k."
- Group varieties, printed p. 13: "Therefore “group variety” = “smooth
  algebraic group”." The same page: "In characteristic zero, all algebraic
  groups are smooth (3.23, 8.39 below)."

The provenance is derived for these reasons.

- Group varieties. Milne's connected group variety over `ℚ` is an affine
  algebraic group (group scheme of finite type) over `ℚ` that is smooth and
  connected (pp. 4, 13, 544). The Lean hypotheses are `IsAffine G.X.left`,
  `Smooth G.X.hom` and `ConnectedSpace G.X.left`; finite type follows, as
  explained above. Since `Spec ℚ` is affine, `IsAffine G.X.left` is
  equivalent to affineness of the structure morphism. In characteristic zero
  the smoothness hypothesis is automatic for algebraic groups (p. 13), but
  it is kept because the Lean statement does not assume finite type
  separately.
- Density. Milne writes "G(Q) is dense in G(R)", regarding `G(ℚ)` as a
  subset of `G(ℝ)`. The Lean statement uses the range of the change-of-rings
  map, which is injective, so the meaning is the same.
- Real topology. Milne does not define the real topology. The Lean statement
  uses the Library's evaluation topology, which is the usual topology, as
  explained in the Statement section.
- Universes. `ℚ` and `ℝ` live in `Type`, so the statement has no universe
  parameter.

Sanity check. For `G = 𝔾_m` the statement says that `ℚ^×` is dense in
`ℝ^×`, and for `G = GL_n` that `GL_n(ℚ)` is dense in `GL_n(ℝ)`. Connectedness
cannot be dropped. The twist of the constant group `ℤ/3ℤ` by the quadratic
character of `ℚ(√2)/ℚ`, acting by negation, is a smooth affine group over
`ℚ`. Its only rational point is the identity, while it has three real
points, since `√2` is real; its real points form a discrete space.

Relation to the Library. The Library has no statement of Theorem 25.70.
`ConnectedGroupUnirationalityStatement` (in
[`Rational.ConnectedGroupUnirationalityStatement`](ConnectedGroupUnirationalityStatement.md))
states Milne's Theorem 17.93, unirationality of connected group varieties over
a perfect field and of connected reductive groups, which Milne's proof uses.
Theorem 25.54, also used by Milne's proof, is not in the Library; it is the
subject of a separate statement candidate, `RealPointComponentsStatement`.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Theorem 25.70 on
printed p. 567 with the same statement; its proof, on printed pp. 567-568,
follows the same steps, and the three sentences quoted below appear there
with the same wording. It has the convention "After p. 162, all algebraic groups are
affine" on printed p. 4, and "“group variety” = “smooth algebraic group”" on
printed p. 14. Its chapter 25 opening (printed p. 547) omits the affineness
reminder.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 4, 13, 544 or 564. The errata snapshot of 2026-11-04 for
the 2022 reprint (source ID `milne-2022-algebraic-groups-errata-2026-11-04`,
SHA-256 `78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`)
has no entry for printed pp. 4, 14, 547, 567 or 568.

## For the later proof (not part of this unit)

Milne's proof (2017, p. 564) proceeds through tori, groups of multiplicative
type and reductive groups. It begins: "For a torus of the form (G_m)_{k/Q}
(hence for all induced tori) the statement follows from the weak
approximation theorem in algebraic number theory." For reductive groups it
uses an exact sequence 1 → N → G' × T → G → 1 with `G'` simply connected,
`T` a torus and `N` of multiplicative type, and states: "The real
approximation theorem holds for G' because it is unirational (17.93) and
G'(R) is connected (25.54)." It ends: "Finally, let G be connected group
variety over Q. Because we are in characteristic zero, G is the semidirect
product of a unipotent group and a reductive group (Section f) and the
underlying scheme of a unipotent group is isomorphic to A^n (see 14.66)."
