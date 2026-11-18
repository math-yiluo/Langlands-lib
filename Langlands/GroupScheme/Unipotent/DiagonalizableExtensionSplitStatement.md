# Extensions of a smooth connected unipotent group by a diagonalizable group

`Langlands.GroupScheme.PerfectDiagonalizableUnipotentExtensionSplitStatement.{u}`
is a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field with `[PerfectField k]` and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Let `D` and `U`
be group schemes over `Spec k` with homomorphisms `i : D ⟶ G` and
`q : G ⟶ U`, and assume:

- `IsClosedSubgroup i` and
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`;
- there are `Λ : Type u` with `[AddCommGroup Λ]` and `AddGroup.FG Λ` and an
  isomorphism of group schemes
  `D ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`;
- `Smooth U.X.hom`, `ConnectedSpace U.X.left` and `IsUnipotent U`.

The conclusion is the conjunction of two parts.

1. **Unique section.** There is exactly one homomorphism `s : U ⟶ G` with
   `s ≫ q = 𝟙 U`.
2. **Direct product.** For every homomorphism `s : U ⟶ G` with
   `s ≫ q = 𝟙 U`:
   - for every scheme `T` over `Spec k` and all points `x : T ⟶ D.X` and
     `y : T ⟶ U.X`,
     `(x ≫ i.hom.hom) * (y ≫ s.hom.hom) = (y ≫ s.hom.hom) * (x ≫ i.hom.hom)`
     (the product of points of `G.X` on `T`);
   - `IsIso (subgroupMultiplication i s)`.

The ingredients are existing declarations, used without change.

- `PerfectField k` (Mathlib) says that every irreducible polynomial over `k`
  is separable. `Smooth` (Mathlib) is smoothness of a morphism of schemes;
  `ConnectedSpace U.X.left` says that the underlying topological space of
  `U` is connected (in particular nonempty). `AddGroup.FG Λ` (Mathlib) says
  that `Λ` is finitely generated.
- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι q` (from
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) equals `N` on
  every test scheme. `SubgroupFunctor.range i` (from
  [`SubgroupFunctor`](../SubgroupFunctor.md)) is the subgroup functor of
  points of `G` that factor through `i`.
- `Diagonalizable.groupScheme (CommRingCat.of k) Λ` (from
  [`Torus.Diagonalizable`](../Torus/Diagonalizable.md)) is the
  diagonalizable group `D(Λ) = Spec k[Λ]` over `Spec k`.
- `subgroupMultiplication i s` (from
  [`Rational.LeviSubgroup`](../Rational/LeviSubgroup.md)) is the morphism
  `D.X ⊗ U.X ⟶ G.X` of schemes over `Spec k` sending a point `(x, y)` to
  `i(x) · s(y)`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 16.28, pp.333–334: "Let e → D → G → U → e (119) be an exact
  sequence of algebraic groups over a perfect field. If D is diagonalizable
  and U is smooth, connected, and unipotent, then the sequence has a unique
  splitting: G ≃ D × U." Its proof begins: "Because U is connected, it acts
  trivially on D (see 12.37). If s: U → G is a section, then s(U) = G_u, and
  s is uniquely determined." The existence of a section is proved by
  induction on the dimension of `U`, using a central subgroup of `U`
  isomorphic to `G_a` (16.23) and 15.25.
- Definition 1.61, p.24: "A sequence of algebraic groups e → N → G → Q (3)
  is exact if i is an isomorphism of N onto the kernel of q. A sequence
  e → N → G → Q → e (4) is exact if in addition q is faithfully flat."
- Theorem 12.8, p.233: "An algebraic group G is diagonalizable if and only if
  it is isomorphic to D(M) for some commutative group M."
- Corollary 12.37, p.244: "Every action μ: G × H → H by group homomorphisms
  of a connected algebraic group G on a group H of multiplicative type is
  trivial."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 16.28 and
its proof with the same words, on printed p.334.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.24, 135, 233,
333 or 334. Their p.244 entry concerns 12.41 (`N` should be central), not
Corollary 12.37. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern the affineness sentence. The 2022 errata have no entry
for pp.24, 135, 233, 244, 324, 333 or 334.

## Derivation from the source

- **Algebraic groups.** Milne's algebraic groups are group schemes of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom` for `G`; an affine
  morphism is quasi-compact, so `G` is of finite type over `k`. `D` is
  isomorphic to `D(Λ)` with `Λ` finitely generated, hence affine of finite
  type. `U` is smooth, hence locally of finite type; it is affine of finite
  type as a quotient of `G` (Milne's quotients of affine algebraic groups
  are affine algebraic groups), so no further hypothesis on `U` is imposed.
- **The exact sequence.** By Definition 1.61, exactness says that `i` is an
  isomorphism of `D` onto the kernel of `q` and that `q` is faithfully flat.
  The kernel is a closed subscheme, so `i` is a closed immersion
  (`IsClosedSubgroup i`). `IsFppfQuotient` says that `q` is flat and
  surjective (faithfully flat) and that the actual kernel of `q` has the
  same points as `D` on every test scheme; since `i` and `kernelι q` are
  monomorphisms, this identifies `D` with the kernel. `IsFppfQuotient` also
  asks that `q` be locally of finite presentation, which holds automatically
  because `G` and `U` are of finite type over a field.
- **Diagonalizable.** By Theorem 12.8 a diagonalizable algebraic group is
  isomorphic to `D(M)` for a commutative group `M`, finitely generated
  because `D(M)` is of finite type. This is the existential hypothesis on
  `D`.
- **Unique splitting.** A splitting of the sequence is a section `s` of `q`
  that is a homomorphism of algebraic groups. "The sequence has a unique
  splitting" is part 1. "`G ≃ D × U`" is part 2: with a section `s`, `G` is
  the direct product of `D` and `s(U)`. This means that the points of `D`
  and of `s(U)` commute on every test scheme, as the proof notes (`U` acts
  trivially on `D`), so that multiplication `D × U → G` is a homomorphism,
  and that this multiplication is an isomorphism. A homomorphism of group
  schemes is an isomorphism exactly when its underlying morphism of schemes
  is one, so the second condition is `IsIso (subgroupMultiplication i s)`.
  Part 2 is stated for every section; by part 1 there is exactly one.
- **Universes.** One universe `u` is used for the field, the character group
  `Λ` and the schemes. This is a formalization convention.
