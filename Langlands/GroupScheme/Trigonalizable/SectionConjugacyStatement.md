# Sections and maximal diagonalizable subgroups of trigonalizable groups

`Langlands.GroupScheme.TrigonalizableSectionConjugacyStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be an algebraically closed field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Let `U` be a
group scheme over `Spec k` with a homomorphism `i : U ⟶ G`, let
`Λ : Type u` satisfy `[AddCommGroup Λ]` and `[AddGroup.FG Λ]`, write
`D(Λ)` for `(Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`, and let
`q : G ⟶ D(Λ)` be a homomorphism. Assume `IsClosedSubgroup i`,
`IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal` and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`.

Write `IsDiag S` for: there are `Λ' : Type u` with `[AddCommGroup Λ']` and
`AddGroup.FG Λ'` and an isomorphism of group schemes
`S ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp`. The
conclusion is the conjunction of two parts.

1. **(a) Sections are conjugate.** For all homomorphisms
   `s₁ s₂ : D(Λ) ⟶ G` with `s₁ ≫ q = 𝟙` and `s₂ ≫ q = 𝟙`, there is a point
   `u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X` (a `k`-rational point
   of `U`) such that `s₂ = s₁ ≫ (G.innerIso (u ≫ i.hom.hom)).hom`.
2. **(b) Maximal diagonalizable subgroups.** For every group scheme `S` over
   `Spec k` and every homomorphism `j : S ⟶ G` with `IsClosedSubgroup j` and
   `IsDiag S`, the following are equivalent:
   - for every `j' : S' ⟶ G` with `IsClosedSubgroup j'` and `IsDiag S'`,
     `SubgroupFunctor.range j ≤ SubgroupFunctor.range j'` implies
     `SubgroupFunctor.range j = SubgroupFunctor.range j'`;
   - there is a homomorphism `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙` and
     `SubgroupFunctor.range j = SubgroupFunctor.range s`.

The ingredients are existing declarations, used without change.

- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `SubgroupFunctor.range i` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `i`, on every
  test scheme over `Spec k`. `IsNormal` says that, on every test scheme,
  these points form a normal subgroup of the points of `G`. The order `≤` is
  inclusion of these subgroups on every test scheme.
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
- `G.innerIso g` (from [`InnerAutomorphism`](../InnerAutomorphism.md)) is the
  group-scheme automorphism of `G` given on points over every test scheme by
  conjugation `x ↦ g x g⁻¹` with the pulled-back point `g`, for a point `g`
  of `G` over the base.
- `IsAlgClosed k` and `AddGroup.FG Λ` (`Λ` is finitely generated) are from
  Mathlib.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Theorem 16.27, p.333: "Let G be a trigonalizable algebraic group over an
  algebraically closed field k, and let q: G → D be the quotient of G by
  G_u. (a) Let s1, s2: D → G be sections of q (as a homomorphism of algebraic
  groups). Then there exists a u ∈ G_u(k) such that s2 = inn(u) ∘ s1.
  (b) The maximal diagonalizable subgroups of G are those of the form s(D)
  with s a section of q; any two are conjugate by an element of G_u(k)."
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
one-based PDF page is the printed page plus 11) states Theorem 16.27 on
printed p.333 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.24, 135, 233,
325, 326 or 333. Their p.18 entry concerns the proof of Proposition 1.40,
not Proposition 1.41. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern Proposition 16.2 or the affineness sentence. The 2022
errata have no entry for pp.24, 135, 233, 324, 325, 326 or 333; their p.18
entry concerns the proof of Proposition 1.37.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **Trigonalizable `G` and the quotient by `G_u`.** The hypotheses on `i`
  and `q` are condition (d) of Proposition 16.2, with the quotient `G/U`
  presented as `D(Λ)`: `U` is a normal unipotent algebraic subgroup (a
  closed subgroup), and `q` is a quotient map with kernel `U` onto a
  diagonalizable group, which by Theorem 12.8 may be taken to be `D(Λ)` with
  `Λ` finitely generated (as `G/U` is of finite type). By Proposition 16.2
  such a `G` is trigonalizable, and every trigonalizable `G` admits such `i`
  and `q`. Since a diagonalizable group is of multiplicative type, `U` is
  `G_u` (Notation 16.7, unique by Theorem 16.6) and `q` is the quotient of
  `G` by `G_u`. `IsFppfQuotient` expresses the quotient map: flat and
  surjective (faithfully flat, Definition 1.61), locally of finite
  presentation (automatic between schemes of finite type over a field), with
  kernel `U`. The statement does not mention trigonalizability itself.
- **(a).** A section of `q` as a homomorphism of algebraic groups is a
  group-scheme homomorphism `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙`. An element of
  `G_u(k)` is a `k`-rational point `u` of `U`, that is, a morphism over
  `Spec k` from `Spec k` itself to `U`. `inn(u)` is conjugation by the
  corresponding point `u ≫ i.hom.hom` of `G`, which is
  `(G.innerIso (u ≫ i.hom.hom)).hom`; `inn(u) ∘ s₁` is written
  `s₁ ≫ inn(u)` in diagrammatic order.
- **(b).** A diagonalizable subgroup is a closed subgroup `j : S ⟶ G`
  (Proposition 1.41, p.18: algebraic subgroups are closed) with `S`
  diagonalizable, that is (Theorem 12.8) `IsDiag S`. Maximality among
  diagonalizable subgroups is the displayed condition on ranges. "Of the
  form `s(D)`" means that the subgroup has the same points as the image of a
  section `s`, which is `range j = range s`. The final clause of (b), that
  any two maximal diagonalizable subgroups are conjugate by an element of
  `G_u(k)`, is not stated separately: it follows from (a) and the
  characterization in (b), since `range (s₁ ≫ inn(u))` is the image of
  `range s₁` under `inn(u)`.
- **Universes.** One universe `u` is used for the field, the character
  groups and the schemes. This is a formalization convention.
