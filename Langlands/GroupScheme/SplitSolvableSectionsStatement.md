# Sections of the canonical extension of a split solvable group

`Langlands.GroupScheme.SplitSolvableExtensionSectionsStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let `G : GroupScheme (Spec (CommRingCat.of k))`
satisfy `IsSplitSolvableGroupScheme G`. Let `U` and `D` be group schemes over
`Spec k` with homomorphisms `i : U ⟶ G` and `q : G ⟶ D`, and assume
`IsClosedSubgroup i`, `IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal`,
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` and
`IsMultiplicativeType D`. The conclusion is the conjunction of three parts.

1. **The extension splits.** There is a homomorphism `s : D ⟶ G` with
   `s ≫ q = 𝟙 D`.
2. **Sections are conjugate.** For all homomorphisms `s₁ s₂ : D ⟶ G` with
   `s₁ ≫ q = 𝟙 D` and `s₂ ≫ q = 𝟙 D`, there is a point
   `u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X` (a `k`-rational point
   of `U`) such that `s₂ = s₁ ≫ (G.innerIso (u ≫ i.hom.hom)).hom`.
3. **Maximal split tori.** For every group scheme `S` over `Spec k` and every
   homomorphism `j : S ⟶ G` with `IsClosedSubgroup j` and `IsSplitTorus S`,
   the following are equivalent:
   - for every `j' : S' ⟶ G` with `IsClosedSubgroup j'` and
     `IsSplitTorus S'`, `SubgroupFunctor.range j ≤ SubgroupFunctor.range j'`
     implies `SubgroupFunctor.range j = SubgroupFunctor.range j'`;
   - there is a homomorphism `s : D ⟶ G` with `s ≫ q = 𝟙 D` and
     `SubgroupFunctor.range j = SubgroupFunctor.range s`.

The ingredients are existing declarations, used without change.

- `IsSplitSolvableGroupScheme G` (from [`SplitSolvable`](SplitSolvable.md))
  says that `G` is smooth, affine, connected and solvable
  (`IsSolvableGroupScheme`), and has a finite series of closed, smooth,
  connected subgroups, each normal in the previous one with represented fppf
  quotient isomorphic over `k` to `G_a` or `G_m`, ending with the trivial
  group.
- `IsClosedSubgroup i` (from [`Reductive.Basic`](Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `SubgroupFunctor.range i` (from [`SubgroupFunctor`](SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `i`, on every
  test scheme; `IsNormal` and `≤` are tested on every test scheme.
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι q` (from
  [`AbelianScheme.Kernel`](../AbelianScheme/Kernel.md)) equals `N`.
- `IsMultiplicativeType D` (from
  [`Torus.MultiplicativeType`](Torus/MultiplicativeType.md)) says that `D`
  becomes isomorphic to a diagonalizable group `D(Λ)`, `Λ` finitely
  generated, over some field extension of `k`. `IsSplitTorus S` (from
  [`Torus.Split`](Torus/Split.md)) says that `S` is isomorphic over `k` to a
  finite product of copies of `G_m`.
- `G.innerIso g` (from [`InnerAutomorphism`](InnerAutomorphism.md)) is the
  inner automorphism of `G` given by conjugation with the pulled-back point
  `g` on every test scheme.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 16.54, p.344: "Let G be a split solvable algebraic group over a
  field k. The canonical extension e → G_u → G → D → e splits, and any two
  sections s1, s2: D → G of q are conjugate by an element of G_u(k). The
  maximal split tori in G are those of the form s(D) with s a section of q
  (and so any two such tori are conjugate by an element of G_u(k))." Its
  proof begins: "As G is trigonalizable (16.52), there does exist such an
  exact sequence."
- Definition 6.33, p.132: "A solvable algebraic group G over k is split if it
  admits a subnormal series G = G_0 ⊃ G_1 ⊃ ⋯ ⊃ G_n = e such that each
  quotient G_i/G_{i+1} is isomorphic to G_a or to G_m."
- Theorem 16.6, pp.325–326: "When these conditions hold, G_u is unique and
  contains every unipotent algebraic subgroup of G." Notation 16.7, p.326:
  "When G is an algebraic group, we use G_u exclusively to denote a normal
  algebraic subgroup such that G_u is unipotent and G/G_u is of
  multiplicative type."
- Theorem 16.27(a), p.333, for the meaning of a section: "Let s1, s2: D → G
  be sections of q (as a homomorphism of algebraic groups)."
- Definition 12.14, p.236: "A torus over k is split if it is isomorphic to a
  product of copies of G_m over k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 16.54 on
printed p.344 with the same words. Its Definition 6.33 (p.132) has the same
wording and adds: "Each term G_i in such a subnormal series is smooth,
connected, and affine (1.62, 5.59, 2.70); in particular, G itself is smooth,
connected, and affine."

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for pp.132, 236, 325, 326, 333
or 344.

## Derivation from the source

- **Split solvable group.** Milne's split solvable group (Definition 6.33)
  has a subnormal series with quotients `G_a` or `G_m`; it is smooth,
  connected and affine, as the 2022 reprint notes, and solvable. This is
  `IsSplitSolvableGroupScheme G`, whose series consists of closed subgroups,
  each normal in the previous one, with represented fppf quotients over `k`.
- **The canonical extension.** `G_u` and `D = G/G_u` are as in Notation 16.7:
  a normal unipotent algebraic subgroup (a closed subgroup) with quotient of
  multiplicative type. The hypotheses on `i` and `q` say exactly this, with
  the quotient map `q` expressed by `IsFppfQuotient` (flat, surjective,
  locally of finite presentation, with kernel `U`). By the uniqueness in
  Theorem 16.6, any such `U` is `G_u`; such `i` and `q` exist for split
  solvable `G` by the proof's appeal to 16.52, and that existence is not part
  of the statement.
- **Sections and conjugacy.** A section is a homomorphism `s : D ⟶ G` with
  `s ≫ q = 𝟙 D`. An element of `G_u(k)` is a `k`-rational point `u` of `U`;
  conjugation `inn(u)` is `G.innerIso (u ≫ i.hom.hom)`, and `inn(u) ∘ s₁` is
  written `s₁ ≫ inn(u)` in diagrammatic order.
- **Maximal split tori.** A split torus in `G` is a closed subgroup
  `j : S ⟶ G` with `S` a split torus (Definition 12.14); maximality is among
  closed split tori, by inclusion of ranges. "Of the form `s(D)`" is
  `range j = range s` for a section `s`. The parenthetical conjugacy of
  maximal split tori follows from parts 2 and 3 and is not stated
  separately.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
