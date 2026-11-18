# Splitting of trigonalizable groups

`Langlands.GroupScheme.TrigonalizableExtensionSplitStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Let `U` be a
group scheme over `Spec k` with a homomorphism `i : U ⟶ G`, let
`Λ : Type u` satisfy `[AddCommGroup Λ]` and `[AddGroup.FG Λ]`, write
`D(Λ)` for `(Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`, and let
`q : G ⟶ D(Λ)` be a homomorphism. Assume

- `IsClosedSubgroup i`, `IsUnipotent U` and
  `(SubgroupFunctor.range i).IsNormal`;
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`;
- one of the three cases holds:
  - (a) `IsAlgClosed k`;
  - (b) `PerfectField k`, `Smooth U.X.hom` and `ConnectedSpace U.X.left`;
  - (c) `PerfectField k` and `ConnectedSpace D(Λ).X.left`.

Then there is a homomorphism `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙 D(Λ)`.

The ingredients are existing declarations, used without change.

- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `SubgroupFunctor.range i` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `i`, on every
  test scheme over `Spec k`. `IsNormal` says that, on every test scheme,
  these points form a normal subgroup of the points of `G`.
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι q` (from
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) equals `N` on
  every test scheme.
- `Diagonalizable.groupScheme (CommRingCat.of k) Λ` (from
  [`Torus.Diagonalizable`](../Torus/Diagonalizable.md)) is the
  diagonalizable group `D(Λ) = Spec k[Λ]` over `Spec k`.
- `IsAlgClosed k`, `PerfectField k` (every irreducible polynomial over `k` is
  separable), `AddGroup.FG Λ` (`Λ` is finitely generated) and `Smooth` are
  from Mathlib. `ConnectedSpace X.left` says that the underlying topological
  space of `X` is connected (in particular nonempty).

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Theorem 16.26, p.332: "Let G be a trigonalizable algebraic group over a
  field k. The extension e → G_u → G → D → e splits in each of the following
  cases: (a) the field k is algebraically closed; (b) the field k is perfect
  and G_u is smooth and connected; (c) the field k is perfect and D is
  connected."
- Proof of Theorem 16.26, p.333: "It remains to show that the top extension
  splits, because, if d ↦ (s(d), g) is a section of G ×_{G/N} D → D, then
  d ↦ s(d) is a section of G → D."
- Theorem 16.27(a), p.333, for the meaning of a section: "Let s1, s2: D → G
  be sections of q (as a homomorphism of algebraic groups)."
- Proposition 16.2, pp.324–325: "The following conditions on an algebraic
  group G are equivalent: (a) G is trigonalizable; ... (d) there exists a
  normal unipotent algebraic subgroup U of G such that G/U is
  diagonalizable."
- Theorem 16.6, pp.325–326: "When these conditions hold, G_u is unique and
  contains every unipotent algebraic subgroup of G." Notation 16.7, p.326:
  "When G is an algebraic group, we use G_u exclusively to denote a normal
  algebraic subgroup such that G_u is unipotent and G/G_u is of
  multiplicative type."
- Theorem 12.8, p.233: "An algebraic group G is diagonalizable if and only if
  it is isomorphic to D(M) for some commutative group M."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- Definition 1.61, p.24: "A sequence of algebraic groups e → N → G → Q (3)
  is exact if i is an isomorphism of N onto the kernel of q. A sequence
  e → N → G → Q → e (4) is exact if in addition q is faithfully flat."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Theorem 16.26 on
printed p.332 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.24, 135, 233,
325, 326, 332 or 333. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern Proposition 16.2 or the affineness sentence. The 2022
errata have no entry for pp.24, 135, 233, 324, 325, 326, 332 or 333.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **Trigonalizable `G` with its extension.** The hypotheses on `i` and `q`
  are condition (d) of Proposition 16.2, with the quotient `G/U` presented
  as `D(Λ)`: `U` is a normal unipotent algebraic subgroup (a closed
  subgroup), and `q` is a quotient map with kernel `U` onto a diagonalizable
  group, which by Theorem 12.8 may be taken to be `D(Λ)` with `Λ` finitely
  generated (as `G/U` is of finite type). By Proposition 16.2 such a `G` is
  trigonalizable, and every trigonalizable `G` admits such `i` and `q`. Since
  a diagonalizable group is of multiplicative type, `U` is `G_u` in the sense
  of Notation 16.7, unique by Theorem 16.6, and `D(Λ)` is the group `D = G/G_u`
  of Theorem 16.26. The statement therefore does not mention trigonalizability
  itself.
- **The quotient map.** Milne's quotient map is faithfully flat (Definition
  1.61 for exact sequences). `IsFppfQuotient` says that `q` is flat and
  surjective, that it is locally of finite presentation (automatic between
  schemes of finite type over a field), and that the actual kernel of `q`
  has the same points as `U` on every test scheme; since `i` and `kernelι q`
  are monomorphisms, this identifies the kernel with `U`. Milne tests
  normality on points with values in `k`-algebras; `IsNormal` tests every
  scheme over `Spec k`, which gives the same condition because `U` is closed
  in `G`.
- **Splitting.** The extension splits when `q` has a section that is a
  homomorphism of algebraic groups, as in the quoted sentences. This is a
  group-scheme homomorphism `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙`.
- **The three cases.** They are stated as a disjunction of hypotheses, with
  smoothness and connectedness of `G_u = U` and connectedness of `D = D(Λ)`
  as properties of the underlying morphism of schemes and topological space.
- **Universes.** One universe `u` is used for the field, the character group
  `Λ` and the schemes. This is a formalization convention.
