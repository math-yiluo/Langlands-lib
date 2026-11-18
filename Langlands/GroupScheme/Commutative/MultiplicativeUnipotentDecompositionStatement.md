# Multiplicative and unipotent parts of a commutative algebraic group

`Langlands.GroupScheme.CommutativeMultiplicativeUnipotentDecompositionStatement.{u}`
is a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and
`[IsCommMonObj G.X]`. The statement is the conjunction of two parts.

1. **(a) The multiplicative part.** There are group schemes `S` and `Q` over
   `Spec k` and homomorphisms `s : S ⟶ G` and `q : G ⟶ Q` such that:
   - `IsClosedSubgroup s` and `IsMultiplicativeType S`;
   - *largest:* for every group scheme `H` over `Spec k` and every
     homomorphism `h : H ⟶ G` with `IsClosedSubgroup h` and
     `IsMultiplicativeType H`,
     `SubgroupFunctor.range h ≤ SubgroupFunctor.range s`;
   - *characteristic:* for every `R : Type u` with `[CommRing R]` and
     `[Algebra k R]`, write `F` for the base-change functor
     `GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))`;
     then for every isomorphism `α : F.obj G ≅ F.obj G` of group schemes over
     `Spec R`,
     `SubgroupFunctor.range (F.map s ≫ α.hom) = SubgroupFunctor.range (F.map s)`;
   - *unipotent quotient:*
     `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q` and
     `IsUnipotent Q`.
2. **(b) Perfect fields.** If `PerfectField k`, then both of the following
   hold.
   - *Existence:* there are group schemes `U` and `S` over `Spec k` and
     homomorphisms `u : U ⟶ G` and `s : S ⟶ G` with `IsClosedSubgroup u`,
     `IsUnipotent U`, `IsClosedSubgroup s`, `IsMultiplicativeType S` and
     `IsIso (subgroupMultiplication u s)`.
   - *Uniqueness:* for all `U`, `S`, `u : U ⟶ G` and `s : S ⟶ G` satisfying
     these five conditions, `range j ≤ range u` for every closed subgroup
     `j : V ⟶ G` with `IsUnipotent V`, and `range h ≤ range s` for every
     closed subgroup `h : H ⟶ G` with `IsMultiplicativeType H`. Here
     `range` is `SubgroupFunctor.range`.

The ingredients are existing declarations, used without change.

- `IsCommMonObj G.X` (Mathlib) says that the multiplication of the group
  object `G.X` is commutative.
- `IsClosedSubgroup s` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `s` is a closed immersion.
  `IsUnipotent Q` (same module) says that every nonzero finite-dimensional
  matrix representation of `Q` has a nonzero fixed vector (Milne 6.45).
- `IsMultiplicativeType S` (from
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md)) says that
  there are a field extension `L : Type u` of `k` and a finitely generated
  commutative group `Λ : Type u` such that `S_L` is isomorphic, as a group
  scheme, to the diagonalizable group `D(Λ)` over `L`.
- `SubgroupFunctor.range s` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `s`, on every
  test scheme over the base. The order `≤` is inclusion of these subgroups
  on every test scheme.
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along `Spec R ⟶ Spec k`, as a functor; `F.map s`
  is the base-changed homomorphism `S_R ⟶ G_R`.
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι q` (from
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) equals `N` on
  every test scheme.
- `subgroupMultiplication u s` (from
  [`Rational.LeviSubgroup`](../Rational/LeviSubgroup.md)) is the morphism
  `U.X ⊗ S.X ⟶ G.X` of schemes over `Spec k` sending a point `(x, y)` to
  `u(x) · s(y)`.
- `PerfectField k` (Mathlib) says that every irreducible polynomial over `k`
  is separable.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Theorem 16.13, p.328: "Let G be a commutative algebraic group over k.
  (a) There exists a largest algebraic subgroup G_s of G of multiplicative
  type; this is a characteristic subgroup of G, and the quotient G/G_s is
  unipotent. (b) If k is perfect, then there also exists a largest unipotent
  algebraic subgroup G_u of G, and G ≃ G_u × G_s (unique decomposition of G
  into a product of a unipotent subgroup and a subgroup of multiplicative
  type)."
- Proof of Theorem 16.13(b), p.328: "If G = U × M with U unipotent and M
  multiplicative, then the decomposition is unique (and M = G_s). Indeed, if
  U′ is a unipotent subgroup of G, then the map U′ → G → G/U ≃ M is trivial
  (14.18), and so U′ ⊂ U. Similarly, M contains every subgroup of
  multiplicative type."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- Definition 1.51(b), p.21: "An algebraic subgroup H of G is characteristic
  if α(H_R) = H_R for all small k-algebras R and all automorphisms α of
  G_R." The following sentence: "The conditions hold for all k-algebras R if
  they hold for all small k-algebras."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
- Definition 12.17, p.236: "An algebraic group over k is of multiplicative
  type if it becomes diagonalizable over some field containing k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map
  if it is faithfully flat." and "Thus a homomorphism is a quotient map if it
  is both flat and surjective."
- After Theorem 5.13, p.101: "It follows that a quotient map q: G → Q is
  uniquely determined by its kernel N up to a unique isomorphism. We denote
  any such map by q: G → G/N and call G/N the quotient of G by N."
  Theorem 5.14, p.102: "Every normal algebraic subgroup N of an algebraic
  group G arises as the kernel of a quotient map G → Q."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Theorem 16.13 and its
proof on printed p.328 with the same words. Its Definition 1.51(b), p.21,
reads "for all k-algebras R" instead of "for all small k-algebras R".

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.99, 101, 102,
135, 236, 312, 328 or 329. Their p.18 entry concerns the proof of
Proposition 1.40, not Proposition 1.41. Their p.21 entry concerns
Definition 1.48, not Definition 1.51. Their p.324 entry replaces
"diagonalizable" with "trigonalizable" in the last sentence of the first
paragraph of Chapter 16; it does not concern the affineness sentence. The
2022 errata have no entry for pp.21, 99, 101, 102, 135, 236, 312, 324, 328
or 329; their p.18 entry concerns the proof of Proposition 1.37. Their p.321
entry says that Theorem 15.37 needs the groups to be commutative, and adds:
"The result is only used in the proof of 16.13, where the groups are
commutative." So the correction does not affect Theorem 16.13.

Milne's proof, for orientation only (the statement does not depend on this
route). (a) `G_s` is the intersection of the algebraic subgroups `H` with
`G/H` unipotent; `G/G_s` embeds in `∏ G/H` and so is unipotent (14.7). Every
homomorphism `G_s → G_a` is trivial, so `G_s` is of multiplicative type
(12.18). A subgroup `H` of multiplicative type maps trivially to `G/G_s`
(14.18), so `H ⊂ G_s`. For an endomorphism `α` of `G_R`, the composite
`(G_s)_R → G_R → G_R → (G/G_s)_R` is trivial (Proposition 15.18, p.312), so
`α((G_s)_R) ⊂ (G_s)_R`; hence `G_s` is characteristic (1.53). (b) The
uniqueness is the argument quoted above. By uniqueness and Galois descent one
may assume `k` algebraically closed; then `e → G_s → G → G/G_s → e` splits
(15.37), giving `G = U × G_s` with `U ≃ G/G_s` unipotent.

## Derivation from the source

- **Commutative algebraic group.** Milne's algebraic group is a group scheme
  of finite type over `k`, affine by the Chapter 16 convention. The
  statement assumes `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`;
  an affine morphism is quasi-compact, so `G` is of finite type over `k`.
  Commutativity is `IsCommMonObj G.X`.
- **Algebraic subgroups.** An algebraic subgroup is a group scheme with a
  homomorphism to `G` that is a closed immersion (Proposition 1.41). A
  closed subgroup of `G` is affine and of finite type over `k`. "Largest"
  means containing every algebraic subgroup of the same kind: every point of
  `G` that factors through `H` factors through `s`, on every test scheme.
  This is `range h ≤ range s`.
- **Multiplicative type.** Milne's Definition 12.17 is "diagonalizable over
  some field containing `k`". By Theorem 12.8 (p.233), a diagonalizable
  algebraic group is isomorphic to `D(Λ)` for a commutative group `Λ`,
  finitely generated because `D(Λ)` is of finite type. This is
  `IsMultiplicativeType`.
- **Characteristic.** For a `k`-algebra `R`, `G_R` and `S_R` are the base
  changes `F.obj G` and `F.obj S`, and `F.map s : S_R ⟶ G_R` is the base
  change of the inclusion. An automorphism `α` of `G_R` is an isomorphism
  `F.obj G ≅ F.obj G` of group schemes over `Spec R`. The subgroup `α(S_R)`
  is the image of `F.map s ≫ α.hom`; its points on every test scheme over
  `Spec R` are `range (F.map s ≫ α.hom)`. So `α(S_R) = S_R` is the displayed
  equality of ranges. Milne tests functors on `R`-algebras or, equivalently
  by the Yoneda lemma (remark after Definition 1.51), on algebraic
  `R`-schemes; the statement tests all schemes over `Spec R`, which have the
  same points because `F.map s ≫ α.hom` and `F.map s` are closed immersions
  and membership of a point can be checked on an affine open cover. The
  algebra `R` lies in the universe `u` of `k`, as Milne's small algebras
  suffice.
- **The quotient.** The quotient `G/G_s` exists (Theorem 5.14) and is
  determined by the kernel of the quotient map up to unique isomorphism
  (after Theorem 5.13). So "`G/G_s` is unipotent" means that there is a
  quotient map `q : G ⟶ Q` with kernel `G_s` and `Q` unipotent. Milne's
  quotient map is a flat surjective homomorphism (Definition 5.5).
  `IsFppfQuotient` also asks that `q` be locally of finite presentation;
  this holds automatically because `G` and `Q` are of finite type over a
  field. Its kernel clause says that the actual kernel of `q` has the same
  points as `S` on every test scheme. No finiteness or affineness hypothesis
  on `Q` is imposed: `Q` is a quotient of an affine algebraic group, so it
  is one too.
- **The decomposition.** Since `G` is commutative, multiplication
  `G × G → G` is a homomorphism, so for subgroups `U` and `S` the map
  `(x, y) ↦ x · y` is a homomorphism `U × S → G`. "`G = U × S`" as a product
  of the two subgroups means that this map is an isomorphism. A homomorphism
  of group schemes is an isomorphism of group schemes exactly when its
  underlying morphism of schemes is an isomorphism, so the condition is
  `IsIso (subgroupMultiplication u s)`.
- **(b): largest unipotent subgroup.** Milne asserts that `G_u` exists, is
  the largest unipotent algebraic subgroup, and that `G ≃ G_u × G_s` is the
  unique such decomposition. The statement gives one decomposition and says
  that in every decomposition the unipotent factor contains every unipotent
  closed subgroup and the multiplicative factor contains every closed
  subgroup of multiplicative type, as in the quoted proof. Together these
  give the largest unipotent subgroup (the factor `U` of the decomposition),
  and show that any two decompositions have the same factors, with
  multiplicative factor `G_s` of part (a). The uniqueness argument does not
  use perfectness, but it is stated under the hypothesis of (b) as in the
  source.
- **Not included.** The remark after the proof on p.329, that `G_s` and
  `G_u` are smooth or connected when `G` is, is not part of this statement.
- **Universes.** One universe `u` is used for the field, the algebras `R`,
  the groups in `IsMultiplicativeType` and the schemes. This is a
  formalization convention.
