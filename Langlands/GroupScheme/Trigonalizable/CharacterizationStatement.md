# Characterizations of trigonalizable groups

`Langlands.GroupScheme.TrigonalizableCharacterizationStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. The statement
is the conjunction of three equivalences, each with `IsTrigonalizable G` on
the left.

1. **(a) ⇔ (b).** `IsTrigonalizable G` holds if and only if, for every finite
   type `n : Type` with `[Fintype n]` and `[DecidableEq n]` and every
   `ρ : MatrixRepresentation G n`, there is a family
   `W : Fin (Fintype.card n + 1) → Submodule k (n → k)` such that `W` is
   monotone, `Module.finrank k (W i) = i.val` for every `i`, and
   `ρ.IsStableSubspace (W i)` for every `i`.
2. **(a) ⇔ (c).** `IsTrigonalizable G` holds if and only if there are
   `N : ℕ` and a homomorphism of group schemes
   `j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
   (fun i => -(i.val : ℤ))` with `IsClosedSubgroup j`.
3. **(a) ⇔ (d).** `IsTrigonalizable G` holds if and only if there are a
   group scheme `U` over `Spec k`, a homomorphism `i : U ⟶ G`, an additive
   commutative group `Λ : Type u` with `AddGroup.FG Λ`, and a homomorphism
   `q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp` such
   that `IsClosedSubgroup i`, `IsUnipotent U`,
   `(SubgroupFunctor.range i).IsNormal`, and
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`.

The ingredients are existing declarations, used without change.

- `IsTrigonalizable G` (from [`Trigonalizable`](../Trigonalizable.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero coordinate vector spanning a stable line: every point of `G`, with
  values in any scheme over `Spec k`, maps it to a multiple of itself. This
  is Milne's Definition 16.1, as recorded in that module.
- `MatrixRepresentation G n` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `G ⟶ GL_n` over `Spec k`, a representation of `G` on `kⁿ`
  with its standard basis.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says: for every commutative `k`-algebra `A`, every point `x` of `G` with
  values in `A`, every `v ∈ W` and every `k`-linear map `ℓ : A → k`,
  applying `ℓ` to the coordinates of `ρ(x)v` gives a vector of `W`.
- `GeneralLinear.blockParabolicScheme n R e` (from
  [`CorepresentedClosedSubgroup`](../CorepresentedClosedSubgroup.md)) is
  the closed subgroup scheme of `GL_n` over `Spec R` cut out by the matrix
  entries `x_ij` with `e i < e j`.
- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `SubgroupFunctor.range i` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `i`, on every
  test scheme over `Spec k`. `IsNormal` says that, on every test scheme,
  these points form a normal subgroup of the points of `G`.
- `Diagonalizable.groupScheme R Λ` (from
  [`Torus.Diagonalizable`](../Torus/Diagonalizable.md)) is the
  diagonalizable group scheme `D(Λ) = Spec R[Λ]`, and `.toGrp` is its
  underlying group scheme.
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι q` (from
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) equals `N` on
  every test scheme.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 16.2, pp.324–325: "The following conditions on an algebraic
  group G are equivalent: (a) G is trigonalizable; (b) every
  finite-dimensional representation (V, r) of G is trigonalizable; (c) G is
  isomorphic to an algebraic subgroup of T_n for some n; (d) there exists a
  normal unipotent algebraic subgroup U of G such that G/U is
  diagonalizable."
- Paragraph before Proposition 16.2, p.324: "A finite-dimensional
  representation (V, r) of an algebraic group G is said to be trigonalizable
  if there exists a basis of V for which r(G) ⊂ T_n. Equivalently, (V, r) is
  trigonalizable if G stabilizes a maximal flag in V."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- 2.9, p.42: `T_n` is the algebraic subgroup of `GL_n` with
  "T_n: R ⇝ {(a_ij) | a_ij = 0 for i > j} (upper triangular matrices)".
- Proposition 4.3, p.85: for a subspace `W` of `V`, the functor
  "R ⇝ G_W(R) = {g ∈ G(R) | g(W_R) = W_R}" is represented by an algebraic
  subgroup `G_W`. The proof of Corollary 4.4, p.85, reads `G_W = G` as "W is
  stable under G".
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
- Definition 1.51(a), p.21: "An algebraic subgroup H of G is normal if
  H(R) is normal in G(R) for all small k-algebras R."
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map
  if it is faithfully flat." and "Thus a homomorphism is a quotient map if it
  is both flat and surjective."
- After Theorem 5.13, p.101: "It follows that a quotient map q: G → Q is
  uniquely determined by its kernel N up to a unique isomorphism. We denote
  any such map by q: G → G/N and call G/N the quotient of G by N."
  Theorem 5.14, p.102: "Every normal algebraic subgroup N of an algebraic
  group G arises as the kernel of a quotient map G → Q."
- Section 12b, p.230: the algebraic group `D(M)` is defined for a finitely
  generated commutative group `M`, with coordinate ring the group algebra
  `k[M]`. Theorem 12.8, p.233: "An algebraic group G is diagonalizable if
  and only if it is isomorphic to D(M) for some commutative group M."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 16.2 and
the paragraph before it on printed pp.324–325 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.42, 99, 101,
102, 230, 233 or 325. Their p.18 entry concerns the proof of
Proposition 1.40, not Proposition 1.41. Their p.21 entry concerns
Definition 1.48, not Definition 1.51. Their p.85 entry says that `G_W` is the stabilizer of `W`
in `G` (not `V`), which is the reading used here. Their p.324 entry replaces
"diagonalizable" with "trigonalizable" in the last sentence of the first
paragraph of Chapter 16; it does not concern Proposition 16.2 or the
affineness sentence. The 2022 errata have no entry for pp.324 or 325.

Milne's proof, for orientation only (the statement does not depend on this
route): (a)⇒(b) by induction on `dim V`, using a stable line `V_1` and a
stable maximal flag in `V/V_1`; (b)⇒(c) by applying (b) to a faithful
finite-dimensional representation (4.9) and using that a monomorphism is a
closed immersion (3.35); (c)⇒(d) with `U = U_n ∩ G`, which is normal and
unipotent (14.5), and `G/U` embeds into the split torus `T_n/U_n`, so it is
diagonalizable (12.9c); (d)⇒(a) because, for a representation `V ≠ 0`, the
subspace `V^U` is nonzero (`U` unipotent) and stable under `G` (5.15), and
`G` acts on it through `G/U`, so it is a sum of one-dimensional
subrepresentations (12.12).

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **(b): representations.** Every finite-dimensional representation is
  isomorphic, by a choice of basis, to a `MatrixRepresentation G n`, and the
  isomorphism carries stable maximal flags to stable maximal flags. So
  quantifying over all `n` and `ρ` covers all finite-dimensional
  representations.
- **(b): maximal flags.** Write `d = Fintype.card n`, the dimension of
  `kⁿ`. A maximal flag in `kⁿ` is a chain `0 = W_0 ⊂ W_1 ⊂ ⋯ ⊂ W_d = kⁿ`
  with `dim W_i = i`. In the statement this is the monotone family `W`
  indexed by `Fin (d + 1)` with `finrank (W i) = i`; dimension `0` forces
  `W 0 = 0`, and dimension `d` forces `W d = kⁿ`. For `n` empty the flag is
  the single subspace `0`.
- **(b): stability.** For a subspace `W`, the subspace `W ⊗ A` of `Aⁿ` is
  the set of vectors all of whose images under `k`-linear maps `ℓ : A → k`,
  applied coordinatewise, lie in `W`. So `ρ.IsStableSubspace W` says that
  `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for every `k`-algebra `A` and every `x ∈ G(A)`.
  Applying it to `x⁻¹` gives equality. This is `G_W = G` in Proposition 4.3,
  that is, `G` stabilizes `W`.
- **(c): `T_N`.** For `n = Fin N` and `e i = -(i.val : ℤ)`, the condition
  `e i < e j` is `j.val < i.val`. So `blockParabolicScheme` is cut out by the
  entries strictly below the diagonal, and its points with values in every
  `k`-algebra are the invertible upper triangular matrices: it is Milne's
  `T_N` (2.9). The same encoding is used in
  `SolvableTriangularEmbeddingStatement` (in
  [`Absolute.SolvableTriangularEmbeddingStatement`](../Absolute/SolvableTriangularEmbeddingStatement.md)).
- **(c): algebraic subgroups.** An algebraic subgroup of `T_N` is a closed
  subgroup scheme (Proposition 1.41). "`G` is isomorphic to an
  algebraic subgroup of `T_N`" therefore means that there is a homomorphism
  `j : G ⟶ T_N` that is a closed immersion, which is `IsClosedSubgroup j`.
  The case `N = 0` is allowed; then `T_0` is trivial.
- **(d): the subgroup `U`.** A normal unipotent algebraic subgroup is a
  group scheme `U` with a homomorphism `i : U ⟶ G` that is a closed
  immersion, with `IsUnipotent U` and normal range. Milne tests normality on
  points with values in every `k`-algebra (Definition 1.51). The Library
  predicate `IsNormal` tests every scheme over `Spec k`. The two agree
  because `U` is closed in `G`: membership of a point in `U` and the
  conjugation identities can be checked on an affine open cover of the test
  scheme.
- **(d): the quotient.** The quotient `G/U` exists (Theorem 5.14) and is
  determined by the kernel of the quotient map up to unique isomorphism
  (after Theorem 5.13). So "`G/U` is diagonalizable" means that there is a
  quotient map with kernel `U` whose target is diagonalizable. By
  Theorem 12.8 the target can be taken to be `D(Λ)` itself, after composing
  with an isomorphism. `Λ` is finitely generated: `D(M)` is defined in
  Section 12b only for finitely generated `M`, and `G/U` is of finite type.
  In the statement `q : G ⟶ D(Λ)` is that quotient map.
- **(d): quotient maps.** Milne's quotient map is a flat surjective
  homomorphism (Definition 5.5). `IsFppfQuotient` also asks that `q` be
  locally of finite presentation. This holds automatically for a morphism
  between schemes of finite type over a field, and `D(Λ)` is of finite type
  because `Λ` is finitely generated. Its kernel clause says that the actual
  kernel of `q` has the same points as `U` on every test scheme. Since `i`
  and `kernelι q` are monomorphisms, this identifies the kernel with `U` as
  subgroup schemes of `G`.
- **Universes.** One universe `u` is used for the field, the group `Λ` and
  the schemes. Every finitely generated commutative group has a copy in
  `Type u`. This is a formalization convention.
