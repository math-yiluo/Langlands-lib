# The dynamic cell of a smooth connected solvable group

`Langlands.GroupScheme.SolvableDynamicCellStatement.{u}` is a proposition
definition. This module defines the proposition and proves nothing.

## Statement

Let `k : Type u` be a field, put `S = Spec (CommRingCat.of k)`, and let
`G : GroupScheme S` satisfy `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`,
`[ConnectedSpace G.X.left]` and `IsSolvableGroupScheme G`. Let
`χ : (Gm S).toGrp ⟶ G` be a cocharacter, and let `U`, `P` be group schemes
over `S` with homomorphisms `iU : U ⟶ G` and `iP : P ⟶ G`. If `iU`
represents `Dynamic.unipotent (-χ)` and `iP` represents
`Dynamic.parabolic χ`, then
`IsIso (SubgroupFunctor.cellMultiplication iU iP)`. Here `-χ` is
`CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ`, the precomposition of
`χ` with inversion of `G_m`.

The ingredients are existing declarations, used without change.

- `IsSolvableGroupScheme G` (from [`Absolute.Borel`](../Absolute/Borel.md))
  says that the abstract group of `k̄`-points of the base change of `G` to
  `k̄ = AlgebraicClosure k` is solvable.
- `Dynamic.parabolic χ` and `Dynamic.unipotent χ` (from
  [`Dynamic.Basic`](Basic.md)) are subgroup functors of `G` on all schemes
  over `S`. A point `g` over `T` lies in `Dynamic.parabolic χ` when its
  conjugation orbit map `T ×_S G_m → G`, `t ↦ χ(t) g χ(t)⁻¹`, extends to
  `T ×_S A¹`; it lies in `Dynamic.unipotent χ` when moreover some such
  extension takes the value `1` along the zero section.
- `SubgroupFunctor.IsRepresentedBy` (from
  [`SubgroupFunctor`](../SubgroupFunctor.md)) requires a monomorphism whose
  range equals the given subgroup functor on every test scheme.
- `SubgroupFunctor.cellMultiplication iU iP` (from
  [`SubgroupFunctor.CellMultiplication`](../SubgroupFunctor/CellMultiplication.md))
  is the morphism `U.X ⊗ P.X ⟶ G.X` over `S` sending `(u, p)` to
  `iU(u) · iP(p)`.
- `Gm.powerHom S (-1)` and `CommGroupScheme.groupHom` are the existing
  inversion endomorphism of `G_m` and its underlying group-scheme
  homomorphism, as in [`Dynamic.FieldOppositeCellStatement`](FieldOppositeCellStatement.md).
- `Smooth` (Mathlib) is smoothness of a morphism of schemes;
  `ConnectedSpace G.X.left` says that the underlying topological space of
  `G` is connected (in particular nonempty).

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 16.35, p.337: "Let G be a smooth connected solvable algebraic
  group over k, and let U_G(λ) and P_G(λ) be the subgroup varieties of G
  attached to a cocharacter λ of G (see 13.30). Then the multiplication map
  U_G(−λ) × P_G(λ) → G is an isomorphism of algebraic varieties."
- Section 13d, p.263: a cocharacter `λ : G_m → G` defines the action
  `(t, g) ↦ λ(t) g λ(t)⁻¹`, written `t · g`. P.264: "P_G(λ) is the closed
  subscheme of G such that P_G(λ)(R) = {g ∈ G(R) | lim_{t→0} t·g exists}
  for all k-algebras R." Proposition 13.29, p.264: "The subfunctor
  R ⇝ {g ∈ G(R) | lim_{t→0} t·g exists and equals e} of G is represented by
  a normal algebraic subgroup U_G(λ) of P_G(λ)."
- Definition 6.26, p.131: "An algebraic group G is solvable if there is a
  subnormal series G = G_0 ⊃ G_1 ⊃ ⋯ ⊃ G_t = e such that each quotient
  G_i/G_{i+1} is commutative." Corollary 6.31, p.132: "Assume that G is
  affine or smooth, and let k′ be a field containing k. Then G is solvable
  if and only if G_{k′} is solvable."
- Proposition 16.34, p.336, over an algebraically closed field: "(c) G is
  smooth and connected, and the abstract group G(k) is solvable; (d) G is
  smooth, connected, and solvable" are equivalent.
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 16.35 on
printed p.337, Proposition 16.34 on p.336 and Corollary 6.31 on p.132, with
the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.131, 132, 263,
264, 336 or 337. Their p.262 entry ("In (86), set Z = X") concerns the
diagram (86) used in the proof of Proposition 13.28, not the definitions of
`P_G(λ)` and `U_G(λ)`. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern the affineness sentence. The 2022 errata have no entry
for pp.131, 132, 263, 264, 324, 336 or 337.

## Derivation from the source

- **The group.** Milne's smooth connected algebraic group is a group scheme
  of finite type over `k`, affine by the Chapter 16 convention. The
  statement assumes `Smooth G.X.hom` (so `G` is locally of finite type),
  `IsAffineHom G.X.hom` (so quasi-compact, hence of finite type) and
  `ConnectedSpace G.X.left`.
- **Solvability.** By Corollary 6.31, `G` is solvable if and only if
  `G_{k̄}` is. `G_{k̄}` is smooth and connected (a connected algebraic group
  is geometrically connected, since it has a rational point), so by
  Proposition 16.34 (c)⇔(d) it is solvable if and only if the abstract group
  `G(k̄)` is solvable. This is `IsSolvableGroupScheme G`.
- **The subgroups `U_G(−λ)` and `P_G(λ)`.** A limit `lim_{t→0} t·g` exists
  when the orbit map on `G_m` extends to `A¹`, and its value is the value of
  the extension at `0`; this is `Dynamic.parabolic χ` and
  `Dynamic.unipotent χ`, tested on all schemes over `S` rather than on
  `k`-algebras. The two agree because `G` is affine, so these conditions
  can be checked on an affine open cover of the test scheme. `−λ` is
  `t ↦ λ(t⁻¹)`, which is `CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ`.
- **Representatives.** Milne uses the actual subgroup varieties. The
  statement allows arbitrary representatives `iU`, `iP`: a monomorphism
  whose range is the given functor on every test scheme is determined up to
  unique isomorphism over `G` (Yoneda), so the multiplication map differs
  from Milne's only by an isomorphism of the source. Existence of
  representatives is not asserted.
- **The conclusion.** "The multiplication map `U_G(−λ) × P_G(λ) → G` is an
  isomorphism of algebraic varieties" is that the morphism of schemes over
  `S` sending `(u, p)` to `u · p` is an isomorphism, which is
  `IsIso (SubgroupFunctor.cellMultiplication iU iP)`.
- **Related Library statements.** `DynamicFieldOppositeCellStatement` (in
  [`Dynamic.FieldOppositeCellStatement`](FieldOppositeCellStatement.md))
  states that this multiplication map is an open immersion for every affine
  algebraic group over a field (Conrad–Gabber–Prasad 2.1.8(3), Milne
  13.33(d)). The present statement asserts that it is an isomorphism when
  `G` is smooth, connected and solvable.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
