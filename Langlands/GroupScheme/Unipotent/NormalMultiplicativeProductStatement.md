# Normal multiplicative and unipotent subgroups with complementary quotients

`Langlands.GroupScheme.NormalMultiplicativeUnipotentProductStatement.{u}` is
a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field, put `S = Spec (CommRingCat.of k)`, and let
`G : GroupScheme S` satisfy `[LocallyOfFiniteType G.X.hom]` and
`[IsAffineHom G.X.hom]`. Let `T`, `U`, `P`, `Q` be group schemes over `S`
with homomorphisms `t : T ⟶ G`, `u : U ⟶ G`, `p : G ⟶ P` and
`q : G ⟶ Q`. Assume:

- `IsClosedSubgroup t`, `(SubgroupFunctor.range t).IsNormal`,
  `IsMultiplicativeType T`,
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range t) p` and
  `IsUnipotent P`;
- `IsClosedSubgroup u`, `(SubgroupFunctor.range u).IsNormal`,
  `IsUnipotent U`,
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range u) q` and
  `IsMultiplicativeType Q`.

Then:

1. for every `V : Over S` and all points `x : V ⟶ T.X`, `y : V ⟶ U.X`,
   `(x ≫ t.hom.hom) * (y ≫ u.hom.hom) = (y ≫ u.hom.hom) * (x ≫ t.hom.hom)`
   in the group of points of `G` over `V`; and
2. `IsIso (subgroupMultiplication t u)`.

The ingredients are existing declarations, used without change.

- `IsClosedSubgroup t` (from [`Reductive.Basic`](../Reductive/Basic.md))
  says that the underlying morphism of schemes of `t` is a closed immersion.
  `IsUnipotent P` (same module) says that every nonzero finite-dimensional
  matrix representation of `P` has a nonzero fixed vector (Milne 6.45).
- `SubgroupFunctor.range t` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `t`, on every
  test scheme over `S`. `IsNormal` says that, on every test scheme, these
  points form a normal subgroup of the points of `G`.
- `RelativeRoot.IsFppfQuotient N p` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `p` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι p` (from
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) equals `N` on
  every test scheme.
- `IsMultiplicativeType T` (from
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md)) says that
  there are a field extension `L : Type u` of `k` and a finitely generated
  commutative group `Λ : Type u` such that `T_L` is isomorphic, as a group
  scheme, to the diagonalizable group `D(Λ)` over `L`.
- `subgroupMultiplication t u` (from
  [`Rational.LeviSubgroup`](../Rational/LeviSubgroup.md)) is the morphism
  `T.X ⊗ U.X ⟶ G.X` over `S` sending `(x, y)` to `t(x) · u(y)`.
- The product `*` of two points of `G` over `V` is the group law on
  morphisms `V ⟶ G.X` given by the group object structure of `G`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Lemma 16.44, p.340: "Let G be an algebraic group, and let T and U be
  normal algebraic subgroups of G. If T is of multiplicative type and G/T is
  unipotent, while U is unipotent and G/U is of multiplicative type, then
  the map (t, u) ↦ tu : T × U → G (122) is an isomorphism"
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- Definition 1.51(a), p.21: "An algebraic subgroup H of G is normal if
  H(R) is normal in G(R) for all small k-algebras R."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map
  if it is faithfully flat." and "Thus a homomorphism is a quotient map if it
  is both flat and surjective."
- After Theorem 5.13, p.101: "It follows that a quotient map q: G → Q is
  uniquely determined by its kernel N up to a unique isomorphism. We denote
  any such map by q: G → G/N and call G/N the quotient of G by N."
  Theorem 5.14, p.102: "Every normal algebraic subgroup N of an algebraic
  group G arises as the kernel of a quotient map G → Q."
- Definition 12.17, p.236: "An algebraic group over k is of multiplicative
  type if it becomes diagonalizable over some field containing k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every
  nonzero representation of G has a nonzero fixed vector."
- Corollary 14.17, p.284: "The intersection of a unipotent algebraic
  subgroup of an algebraic group with an algebraic subgroup of
  multiplicative type is trivial."

Milne's proof, for orientation only: `T ∩ U = e` (14.17). For `t ∈ T(R)`
and `u ∈ U(R)`, `tut⁻¹u⁻¹ ∈ (T ∩ U)(R) = e`, so the map (122) is a
homomorphism. Its kernel is `T ∩ U = e`, and its cokernel is a quotient of
both `G/T` and `G/U`, hence both unipotent and of multiplicative type, hence
trivial (14.17).

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Lemma 16.44 on
printed p.340 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.99, 101, 102,
135, 233, 236, 284 or 340. Their p.18 entry concerns the proof of
Proposition 1.40, not Proposition 1.41. Their p.21 entry concerns
Definition 1.48, not Definition 1.51. Their p.324 entry replaces
"diagonalizable" with "trigonalizable" in the last sentence of the first
paragraph of Chapter 16; it does not concern the affineness sentence. In the
2022 reprint the cited passages are on printed pp.19, 21, 99, 101, 102, 135, 233,
236, 284, 324 and 340, and the 2022 errata have no entry for any of these
pages.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **The normal subgroups.** A normal algebraic subgroup is a group scheme
  with a homomorphism to `G` that is a closed immersion (Proposition 1.41)
  and has normal range. Milne tests normality on points with values in
  `k`-algebras (Definition 1.51). The Library predicate `IsNormal` tests
  every scheme over `S`. The two agree because the subgroup is closed in
  `G`: membership of a point and the conjugation identities can be checked
  on an affine open cover of the test scheme. Normality also follows from
  the quotient hypotheses, since a kernel is normal; it is stated to match
  the source.
- **The quotients.** `G/T` exists (Theorem 5.14), and Milne's quotient map
  is a flat surjective homomorphism (Definition 5.5) whose kernel is `T`.
  So "`G/T` is unipotent" is represented by a homomorphism `p : G ⟶ P`
  with `IsFppfQuotient (range t) p` and `IsUnipotent P`, and likewise
  "`G/U` is of multiplicative type" by `q : G ⟶ Q` with
  `IsFppfQuotient (range u) q` and `IsMultiplicativeType Q`.
  `IsFppfQuotient` also asks that the quotient map be locally of finite
  presentation, which Milne's quotient map is (a morphism between schemes of
  finite type over a field). Conversely, no further hypothesis on `P` or
  `Q` is needed. A morphism that is flat, surjective and locally of finite
  presentation is an fppf covering. By the kernel clause, the morphism
  `G × T → G ×_P G`, `(g, x) ↦ (g, g · t(x))`, is an isomorphism, so `P`
  represents the fppf quotient sheaf of `G` by `T`. Milne's `G/T` represents
  the same sheaf, so `P ≅ G/T` compatibly with the maps from `G`, and the
  same holds for `Q`.
- **Multiplicative type and unipotence.** Milne's Definition 12.17 is
  "diagonalizable over some field containing `k`". A diagonalizable
  algebraic group is isomorphic to `D(Λ)` for a finitely generated
  commutative group `Λ` (Theorem 12.8, p.233), which is
  `IsMultiplicativeType`. Unipotence is Milne's 6.45, which is
  `IsUnipotent`.
- **The conclusion.** Milne's map `(t, u) ↦ tu : T × U → G` is the morphism
  of schemes `subgroupMultiplication t u`. "Is an isomorphism" means an
  isomorphism of algebraic groups `T × U → G`. Such a morphism is a
  homomorphism exactly when the points of `T` and `U` commute: on points
  with values in `V`, `(x₁ x₂, y₁ y₂) ↦ x₁ x₂ y₁ y₂` equals
  `x₁ y₁ x₂ y₂` for all points if and only if `x₂ y₁ = y₁ x₂` for all
  points. So the statement asserts clause 1 (commutation) together with
  clause 2 (`IsIso` of the underlying morphism over `S`). The inverse of a
  homomorphism of group schemes whose underlying morphism is an isomorphism
  is again a homomorphism, so the two clauses together are Milne's
  conclusion.
- **Universes.** One universe `u` is used for the field, the groups in
  `IsMultiplicativeType` and the schemes. This is a formalization
  convention.
