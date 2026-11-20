# Isogenies of split reductive groups are determined by the torus and the simple root groups

`Langlands.GroupScheme.SplitIsogenySimpleRootRigidityStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and put `S = Spec (CommRingCat.of k)`. Let
`G G' : GroupScheme S` with `IsConnectedReductive G` and
`IsConnectedReductive G'`, and let `i : T.toGrp ⟶ G`, `i' : T'.toGrp ⟶ G'`
(with `T T' : CommGroupScheme S`) satisfy `IsSplitTorus T.toGrp`,
`IsMaximalTorus i`, `IsSplitTorus T'.toGrp` and `IsMaximalTorus i'`. Let
`ν : cocharacterLattice T` satisfy `IsGenericCocharacter i ν`. Call
`φ : G ⟶ G'` a split isogeny if

- `Surjective φ.hom.hom.left`,
- `IsFinite (kernel φ).X.hom`, and
- there is `f : T.toGrp ⟶ T'.toGrp` with `f ≫ i' = i ≫ φ`.

Let `φ₁ φ₂ : G ⟶ G'` be split isogenies with `i ≫ φ₁ = i ≫ φ₂`, and such
that for every `α ∈ simpleRelativeRoots i ν`, every `X : Over S` and every
`g : X ⟶ G.X` in `(RelativeRoot.subgroup i α).carrier X`,
`g ≫ φ₁.hom.hom = g ≫ φ₂.hom.hom`. Then `φ₁ = φ₂`.

The ingredients are existing declarations, used without change.

- `IsConnectedReductive G` (from [`Reductive.Basic`](Basic.md)) says that
  `G` is smooth, affine and connected over `k`, with trivial geometric
  unipotent radical.
- `IsSplitTorus T.toGrp` (from [`Torus.Split`](../Torus/Split.md)) says
  that `T` is isomorphic, as a group scheme, to a split torus
  `splitTorus S I` (a power of `G_m`) for a finite index type `I`; `IsMaximalTorus i` (from [`Torus.Maximal`](../Torus/Maximal.md))
  says that `i` is a closed subgroup, `T` is a torus, and whenever `i`
  factors as `f ≫ j` through a closed torus `j`, the map `f` is an
  isomorphism.
- `IsGenericCocharacter i ν` (from
  [`Rational.RelativeRoots`](../Rational/RelativeRoots.md)) says that
  `⟨α, ν⟩ ≠ 0` for every root `α` of `T` in `G`. `simpleRelativeRoots i ν`
  (from [`Rational.StandardParabolic`](../Rational/StandardParabolic.md)) is
  the set of roots `α` with `⟨α, ν⟩ > 0` that are not the sum of two such
  roots.
- `RelativeRoot.subgroup i α` (from
  [`Rational.RootSubgroup`](../Rational/RootSubgroup.md)) is the Library's
  root subgroup functor of `α`, defined on every test scheme; its points
  are the points `g` that extend, through the character `α`, to a map on
  `T`-orbits with value `1` at zero.
- `kernel φ` (from [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md))
  is the scheme-theoretic kernel of `φ`. `IsFinite` and `Surjective` are
  from Mathlib: the kernel is finite over `k`, and the underlying map of
  schemes of `φ` is surjective.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 21.63, p.443: "Let φ₁, φ₂: (G, T) → (G′, T′) be isogenies of
  split reductive groups, and let Δ be a base for Φ(G, T). If φ₁ and φ₂
  agree on T and on U_α for all α ∈ Δ, then they agree on G."
- Its proof: "As φ₁ and φ₂ agree on the Borel subgroup U_α·T of G_α, they
  agree on G_α (see 17.21), and these groups generated G (see 21.62)."
- Chapter 21 opening, p.424: "The field k is arbitrary." and "Recall also
  that G is split if some maximal torus T is split, in which case we refer
  to the pair (G, T) as a split reductive group."
- 21.19, p.431: "The root group U_α is the unique T-stable algebraic
  subgroup of G isomorphic to G_a on which T acts through the character α.
  The last condition means that, for every isomorphism u: G_a → U_α,
  t·u(a)·t⁻¹ = u(α(t)a), all t ∈ T(R), a ∈ G_a(R)."
- 2.23, p.46: "A homomorphism φ: G → H of connected group varieties is an
  isogeny if it is surjective (i.e., |φ| is surjective) and its kernel is
  finite."
- Section 23a, p.485: "An isogeny of split reductive groups (G, T) →
  (G′, T′) is an isogeny φ: G → G′ such that φ(T) ⊂ T′."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) has Corollary 21.63 on
printed p.443 with the same statement; its proof reads "these groups
generate G" in place of "generated". It has the quoted sentences of 21.19 on
p.431 with the same words, 2.23 on p.46 and the definition
of isogenies of split reductive groups on p.486, with the same words, and
the quoted Chapter 21 sentence on p.424.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.46, 424, 431, 443
or 485, and none for 21.19. The 2022 errata have no entry for pp.46, 424,
431, 443 or 486. They have one entry for 21.19, filed under p.440: "Should
read "Recall (14.60)" rather than "Recall (14.59)"." This corrects only the
cross-reference in the first sentence of 21.19, which is not quoted above.

## Derivation from the source

- **Split reductive groups.** A reductive group over `k` is
  `IsConnectedReductive`; "`(G, T)` split" means that `T` is a maximal
  torus of `G` that is split: `IsMaximalTorus i` and `IsSplitTorus T.toGrp`.
  The same holds for `(G', T')`. The field is arbitrary.
- **The base.** For a split reductive group, `Φ(G, T)` is the set of roots
  of `T` in `G`, which is the Library's `relativeRoots i` (the roots of `T`
  through `i`). Every base of a root system is the set of indecomposable
  positive roots for the positive system cut out by a vector that pairs
  nonzero with every root, and such a vector can be chosen in the
  cocharacter lattice because the chamber is open. So "let `Δ` be a base"
  is expressed by `IsGenericCocharacter i ν` and
  `Δ = simpleRelativeRoots i ν`, quantified over all generic `ν`.
- **Isogenies.** By 2.23 an isogeny is a homomorphism that is surjective on
  underlying spaces with finite kernel: `Surjective φ.hom.hom.left` and
  `IsFinite (kernel φ).X.hom`. The condition `φ(T) ⊂ T′` of Section 23a is
  the existence of `f` with `f ≫ i' = i ≫ φ`. This definition appears
  after Corollary 21.63 in the book; the statement uses it as the meaning
  of "isogenies of split reductive groups" in 21.63.
- **Agreement on `T`.** "`φ₁` and `φ₂` agree on `T`" is
  `i ≫ φ₁ = i ≫ φ₂`.
- **Agreement on `U_α`.** `U_α` is the root group of `α`. The statement
  uses the Library's root subgroup functor `RelativeRoot.subgroup i α` for
  it, and "agree on `U_α`" means that `φ₁` and `φ₂` agree on every point of
  this functor over every test scheme. Proved Library theorems show that this
  functor is exactly Milne's root group in the present setting. Milne 21.19
  (quoted above) characterizes `U_α`. For an isomorphism `u : G_a → U_α`
  as there, let `x : G_a → G` be `u` followed by the inclusion of `U_α`,
  with `G_a` the Library's one-dimensional vector group
  `VectorGroup.groupScheme (CommRingCat.of k) 1`. Then `x` is a
  monomorphism, and the displayed law of 21.19 is the Library's
  `VectorGroup.IsTorusEquivariant i x α`
  (from [`MatrixRepresentation.TorusEquivariantAdditive`](../MatrixRepresentation/TorusEquivariantAdditive.md)).
  The proved theorem `VectorGroup.IsTorusEquivariant.represents_root`
  (from [`Rational.MonicRootParametrization`](../Rational/MonicRootParametrization.md))
  then shows that `x` represents `RelativeRoot.subgroup i α` on every test
  scheme. It assumes that `G` is connected reductive, that `T` is a split
  maximal torus, that `α` is a root, and that no `n • α` with `n ≥ 2` is a
  root. The last condition always holds here. The proved theorem
  `rootReducedness` (from
  [`Reductive.RootReducednessProof`](RootReducednessProof.md)) says that two
  integrally dependent roots are equal or opposite. So if `n • α` were a
  root, then `(n - 1) • α = 0` or `(n + 1) • α = 0`. The character lattice of
  a split torus is torsion-free, so this would force `α = 0`, but roots are
  nonzero. Hence the points of `RelativeRoot.subgroup i α` over every test
  scheme are exactly the points of `U_α`. The functor is also tied to its
  Kaletha–Prasad and Conrad–Gabber–Prasad construction by the proved
  `RelativeRoot.quotientActionComparison` (from
  [`Rational.QuotientActionComparisonProof`](../Rational/QuotientActionComparisonProof.md)).
  This theorem identifies the functor with the image of the identity-limit
  subgroup of the descended `G_m`-action on a closed representative of the
  kernel centralizer. [`Rational.CyclicRootFunctorComparisonProof`](../Rational/CyclicRootFunctorComparisonProof.md)
  supplies that representative and the fpqc property of the character map
  for a smooth affine group over a field, a split torus and a nonzero
  character.
- **Conclusion.** "They agree on `G`" is `φ₁ = φ₂`.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
