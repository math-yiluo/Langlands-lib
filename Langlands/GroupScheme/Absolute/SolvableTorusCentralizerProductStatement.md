# A connected solvable group is a unipotent subgroup times a torus centralizer

`Langlands.GroupScheme.SolvableTorusCentralizerProductStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be an algebraically closed field, put
`S = Spec (CommRingCat.of k)`, and let `G : GroupScheme S` satisfy
`[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`
and `IsSolvableGroupScheme G`. Let `T : CommGroupScheme S` and
`j : T.toGrp ⟶ G` satisfy `IsClosedSubgroup j` and `IsTorus T.toGrp`. Then
for every `C : GroupScheme S` and `c : C ⟶ G` with
`(torusCentralizer j).IsRepresentedBy c`, there are `U : GroupScheme S` and
`u : U ⟶ G` with `IsClosedSubgroup u`, `IsUnipotent U` and
`Surjective (subgroupMultiplication u c).left`.

The ingredients are existing declarations, used without change.

- `IsSolvableGroupScheme G` (from [`Absolute.Borel`](Borel.md)) says that
  the abstract group of `k̄`-points of the base change of `G` to
  `k̄ = AlgebraicClosure k` is solvable.
- `IsTorus T.toGrp` (from [`Torus.Lattice`](../Torus/Lattice.md)) says that
  `T` becomes a split torus (a finite product of copies of `G_m`) over some
  field extension of `k`.
- `torusCentralizer j` (from
  [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)) is the
  subgroup functor of points `g` of `G` over a test scheme `T'` such that,
  for every morphism `a : V ⟶ T'` of test schemes and every point `t` of `T`
  over `V`, the pullback of `g` to `V` commutes with `j(t)`.
- `SubgroupFunctor.IsRepresentedBy` (from
  [`SubgroupFunctor`](../SubgroupFunctor.md)) requires a monomorphism whose
  range equals the given subgroup functor on every test scheme.
- `IsClosedSubgroup u` and `IsUnipotent U` (from
  [`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `u` is a closed immersion, and every nonzero finite-dimensional
  representation of `U` has a nonzero fixed vector.
- `subgroupMultiplication u c` (from
  [`Rational.LeviSubgroup`](../Rational/LeviSubgroup.md)) is the morphism
  `U.X ⊗ C.X ⟶ G.X` over `S` sending `(x, y)` to `u(x) · c(y)`.
  `Surjective` (Mathlib) is surjectivity of the underlying morphism of
  schemes.
- `IsAlgClosed k` and `Smooth` are from Mathlib; `ConnectedSpace G.X.left`
  says that the underlying topological space of `G` is connected.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Theorem 16.41, p.339: "Let S be a torus in a connected solvable group
  variety G. Then C_G(S) is connected and G = U·C_G(S) with U unipotent
  subgroup of G."
- Section 16e, p.338: "Throughout, G is a connected group variety and k is
  algebraically closed."
- Definition 12.14, p.236: "An algebraic group over k is a torus if it
  becomes isomorphic to a finite product of copies of G_m over some field
  containing k."
- Definition 1.3, p.7: "An algebraic subgroup of an algebraic group
  (G, m_G) over k is an algebraic group (H, m_H) over k such that H is a
  k-subscheme of G and the inclusion map is a homomorphism of algebraic
  groups." Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups
  are closed (in the Zariski topology)."
- p.13: "“group variety” = “smooth algebraic group”."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every
  nonzero representation of G has a nonzero fixed vector."
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

Milne's proof, for orientation only: every element of `S(k)` is
semisimple, and by Lemma 16.42 there is `s ∈ S(k)` with
`C_G(s) = C_G(S)`, so the theorem follows from Theorem 16.40.

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Theorem 16.41 on
printed p.339 and the Section 16e convention on p.338, with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.7, 13, 131,
132, 135, 236, 336, 338 or 339. Their p.18 entry concerns the proof of
1.40, not Proposition 1.41. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern the affineness sentence. In the 2022 reprint the cited
passages are on printed pp.7, 14, 19, 131, 132, 135, 236, 324, 336, 338 and
339. The 2022 errata have no entry for any of these pages except p.7, whose
entry adds a remark after Definition 1.3 (the neutral element of `H`) and
does not change the definition.

## Derivation from the source

- **Scope.** Theorem 16.41 has two clauses. This statement formalizes the
  second, `G = U·C_G(S)`. The first, connectedness of `C_G(S)`, is already
  proved in the Library for every smooth connected affine group over any
  field: `IsTorus.connectedSpace_centralizer` (in
  [`Torus.CentralizerConnected`](../Torus/CentralizerConnected.md)).
- **The group.** A connected solvable group variety over `k` is a smooth
  algebraic group (p.13), affine by the Chapter 16 convention, with
  connected underlying space: `Smooth G.X.hom` (so `G` is locally of finite
  type), `IsAffineHom G.X.hom` (so quasi-compact, hence of finite type) and
  `ConnectedSpace G.X.left`. The field is algebraically closed throughout
  Section 16e.
- **Solvability.** By Corollary 6.31, `G` is solvable if and only if
  `G_{k̄}` is. `G_{k̄}` is smooth and connected (a connected algebraic group
  is geometrically connected, since it has a rational point), so by
  Proposition 16.34 (c)⇔(d) it is solvable if and only if the abstract group
  `G(k̄)` is solvable. This is `IsSolvableGroupScheme G`.
- **The torus.** A torus in `G` is an algebraic subgroup, hence a closed
  subgroup `j : T ⟶ G` (Definition 1.3, Proposition 1.41), with `T` a torus
  (Definition 12.14). `T` is commutative, so it is given as a
  `CommGroupScheme`.
- **The centralizer.** `C_G(S)` is the scheme-theoretic centralizer, whose
  points over a `k`-algebra `R` are the elements of `G(R)` commuting with
  every point of `S` over every `R`-algebra. On all test schemes this is
  `torusCentralizer j`. Milne uses the actual subgroup; the statement allows
  an arbitrary representative `c`. A monomorphism whose range is the given
  functor on every test scheme is determined up to unique isomorphism over
  `G` (Yoneda), so the conclusion does not depend on the choice. Existence
  of a representative is not asserted.
- **The product.** "`U` unipotent subgroup of `G`" is an algebraic subgroup
  (Definition 1.3), hence closed (Proposition 1.41), which is unipotent
  (6.45): `IsClosedSubgroup u` and `IsUnipotent U`. No smoothness or
  connectedness of `U` is asserted, as in the source. "`G = U·C_G(S)`" says
  that every element of `G(k)` is a product `xy` with `x ∈ U(k)` and
  `y ∈ C_G(S)(k)`, that is, the multiplication morphism `U × C_G(S) → G` is
  surjective on `k`-points. As `k` is algebraically closed and all three
  schemes are of finite type over `k`, this is equivalent to surjectivity of
  the morphism of schemes (closed points are `k`-points, nonempty fibres of
  finite type over `k` have `k`-points, and a constructible set containing
  all closed points of a scheme of finite type over `k` is the whole space).
  This is `Surjective (subgroupMultiplication u c).left`.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
