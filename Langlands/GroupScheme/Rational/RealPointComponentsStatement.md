# Connected components of real points

`Langlands.GroupScheme.RealPointComponentsStatement` is a Prop-valued
definition with no universe parameters. This module defines the proposition
and proves nothing.

## Statement

The proposition says: let `G : GroupScheme (Spec (CommRingCat.of ℝ))` be a
group scheme over `ℝ` with `[IsAffine G.X.left]`. Then both of the following
hold.

1. If `IsSimplyConnected G`, then `ConnectedSpace (RingPoint ℝ G.X ℝ)`.
2. If `IsConnectedReductive G`, then
   `Finite (ConnectedComponents (RingPoint ℝ G.X ℝ))`.

In words: for a simply connected semisimple group `G` over `ℝ`, the group
`G(ℝ)` of real points is connected for the real topology. For a connected
reductive group `G` over `ℝ`, the space `G(ℝ)` has only finitely many
connected components.

The ingredients are existing declarations, used without change.

- `GroupScheme S` (from `Langlands.AbelianScheme.GroupScheme`) is
  `Grp (Over S)`, a group object in schemes over `S`. `G.X : Over S` is its
  underlying scheme over `S`, and `G.X.left` is the underlying scheme.
- `RingPoint ℝ G.X ℝ` (from
  [`PointTopology.ProductRingPoints`](../../AlgebraicGeometry/PointTopology/ProductRingPoints.md))
  is the set of actual morphisms `Spec ℝ ⟶ G.X` over `Spec ℝ`: the real
  points `G(ℝ)`.
- The topology on `RingPoint ℝ G.X ℝ` is the instance of
  [`PointTopology.AffineScheme`](../../AlgebraicGeometry/PointTopology/AffineScheme.md),
  which needs `[IsAffine G.X.left]`. It is induced from the evaluation
  topology on algebra maps `Γ(G.X.left) → ℝ` over `ℝ`: the coarsest topology
  for which every evaluation `p ↦ p(a)`, for `a` a global function, is
  continuous into `ℝ`. This is the real topology of Milne's statement. If
  `x₁, …, xₙ` generate the coordinate ring of an `ℝ`-algebra of finite type,
  every evaluation is a polynomial in the evaluations at the `xᵢ`. So the
  evaluation topology is the subspace topology of the image of
  `p ↦ (p(x₁), …, p(xₙ))` in `ℝⁿ`.
- `IsSimplyConnected G` (from
  [`SimplyConnected.Basic`](../SimplyConnected/Basic.md)) says that `G` is
  semisimple (`IsSemisimple G`) and that every central isogeny `H ⟶ G` from
  a semisimple group `H` is an isomorphism. `IsSemisimple G` (from
  [`Reductive.Semisimple`](../Reductive/Semisimple.md)) is
  `IsConnectedReductive G` together with finiteness of the scheme-theoretic
  centre.
- `IsConnectedReductive G` (from [`Reductive.Basic`](../Reductive/Basic.md))
  says that `G` is smooth, affine (`IsAffineHom G.X.hom`) and connected over
  `ℝ`, and that the unipotent radical of its base change to an algebraic
  closure of `ℝ` is trivial.
- `ConnectedSpace` and `ConnectedComponents` are from Mathlib.
  `Finite (ConnectedComponents X)` says that `X` has finitely many connected
  components.

The binder `[IsAffine G.X.left]` adds no hypothesis to either part. Each of
`IsSimplyConnected G` and `IsConnectedReductive G` includes
`IsAffineHom G.X.hom`, and `Spec ℝ` is affine, so `G.X.left` is affine by
Mathlib's `isAffine_of_isAffineHom`. The binder is needed only to form the
topology. Since `IsAffine` is a proposition, the topology does not depend
on how it is supplied.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statements, printed p. 560:

- Theorem 25.54 (Cartan): "Let G be a semisimple algebraic group over R. If
  G is simply connected, then G(R) is connected."
- Corollary 25.55: "Let G be a reductive algebraic group over R. Then G(R)
  has only finitely many components for the real topology."

The context and definitions:

- Conventions, printed p. 4: "After p. 162, all algebraic groups are
  affine." Chapter 25 opening, printed p. 544: "Recall that all algebraic
  groups are affine over a base field k."
- 6.44 and 6.46, printed p. 135: "A connected group variety over a field k
  is semisimple if G_{k^a} is semisimple, i.e., if its geometric radical
  R(G_{k^a}) is trivial." "A connected group variety over a field k is said
  to be reductive if G_{k^a} is reductive, i.e., if its geometric unipotent
  radical R_u(G_{k^a}) is trivial."
- Proposition 19.15, printed p. 400: "A semisimple group G is simply
  connected if and only if every central isogeny G' → G from a semisimple
  group G' to G is an isomorphism."
- Aside 2.45(b), printed p. 53, uses the same phrase: "An algebraic group G
  over R may be connected without G(R) being connected for the real
  topology, and conversely. For example, GL_2 is connected as an algebraic
  group, but GL_2(R) is not connected".

The provenance is derived for these reasons.

- Group schemes. Milne's semisimple and reductive groups over `ℝ` are
  affine (p. 4, p. 544). They are connected group varieties, that is,
  smooth and connected algebraic groups. `IsConnectedReductive` is Milne's
  reductive group (see [`Reductive.Basic`](../Reductive/Basic.md)). The
  Library's `IsSemisimple` uses the finite-centre characterization of
  semisimplicity among connected reductive groups, as recorded in
  [`Reductive.Semisimple`](../Reductive/Semisimple.md). `IsSimplyConnected`
  is the criterion of Milne's Proposition 19.15. The Lean statement
  quantifies over every affine group scheme over `ℝ`. Each part applies
  under its own hypothesis, which already implies affineness.
- Real topology. Milne does not define the real topology. The Lean
  statement uses the Library's evaluation topology, which is the usual
  topology for affine schemes of finite type over `ℝ`, as explained in the
  Statement section.
- Components. "Finitely many components" is read as finitely many
  connected components of the topological space `G(ℝ)`.
- The two results are stated together in one proposition, as parts 1 and 2,
  because Corollary 25.55 is the reductive companion of Theorem 25.54. The
  Lean statement claims nothing more than the two results.

Sanity check. `GL_n` over `ℝ` is connected reductive but not semisimple, so
part 1 does not apply to it. Part 2 asserts that `GL_n(ℝ)` has finitely many
components; it has two (`det > 0` and `det < 0`). `SL_2` is simply connected,
and `SL_2(ℝ)` is connected. Simple connectivity is needed in part 1:
`PGL_2` is semisimple and `PGL_2(ℝ)` has two components, as the sign of the
determinant is well defined modulo squares.

Relation to the Library. The Library has no statement of Theorem 25.54 or
Corollary 25.55. Related declarations:

- `realSmoothAffineLieGroup` (in
  [`GroupScheme.SmoothAffinePointLieGroup`](../SmoothAffinePointLieGroup.md))
  makes `RingPoint ℝ G.X ℝ` a Lie group for a smooth affine `G` over `ℝ`.
- `smoothAffine_topology_eq_evaluation` (in
  [`PointManifold.SmoothAffineManifold`](../../AlgebraicGeometry/PointManifold/SmoothAffineManifold.md))
  shows that those charts give the same evaluation topology as the
  instance used here.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Theorem 25.54 and
Corollary 25.55 on printed p. 563 with the same statements. Its proof of
25.54 reads "There is a proof in Borel and Tits 1972, 4.7, which is
summarized in Platonov and Rapinchuk 1994, p. 407." Its proof of 25.55, on
printed p. 564, adds: "Alternatively, a theorem of Whitney says that every
algebraic variety over R has only finitely many connected components for the
real topology." It has the convention "After p. 162, all algebraic groups are
affine" on printed p. 4. Its chapter 25 opening (printed p. 547) omits the
affineness reminder. It has 6.44 and 6.46 on printed p. 135 and Proposition
19.15 on printed p. 401 with the same wording.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 4, 53, 135, 400, 544, 560 or 561. The errata snapshot of
2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed pp. 4, 135, 401, 547 or 564. Its only entry for printed p. 563
concerns terminology in Section g (it reads: I sometimes write "cohomology
group" for "cohomology set"). This does not affect Theorem 25.54 or
Corollary 25.55.

## For the later proof (not part of this unit)

Milne gives no self-contained proof of either part.

- Part 1 (2017, p. 560): "If G = (H)_{C/R} for H a connected group variety
  over C, then G(R) = H(C), which is connected for the complex topology. If
  G is absolutely almost-simple, then the statement is proved in Platonov
  and Rapinchuk 1994, Theorem 7.6, p. 407. The general case now follows from
  these two cases (24.3)."
- Part 2 (2017, p. 561): "For a torus, this can be proved directly. For a
  general G, there is an exact sequence e → N → G' × T → G → e (168) with G'
  the simply connected covering of G^der, T the torus Z(G)_t, and N finite.
  The group H^1(R, N) is finite, from which the statement follows." The
  Whitney theorem cited in the 2022 reprint gives part 2 for every affine
  scheme of finite type over `ℝ`.
