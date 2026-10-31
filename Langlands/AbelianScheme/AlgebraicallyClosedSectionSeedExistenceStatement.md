# Finite section seeds at the unit over an algebraically closed field

`Langlands.GroupScheme.AlgebraicallyClosedSectionSeedExistenceStatement`, in module
`Langlands.AbelianScheme.AlgebraicallyClosedSectionSeedExistenceStatement`, is one
universe-polymorphic Prop-valued definition. It is a statement target, with no proof
of the asserted existence. Worker 143 wrote this pair using the Lean statement
specified and previously checked by Worker 1076.

## Exact statement

For an arbitrary universe `u`, the statement quantifies, in order, over a field
`K : Type u`, an instance `IsAlgClosed K`, a group object
`G : Grp (Over (Spec (CommRingCat.of K)))`, and a commutativity instance
`IsCommMonObj G.X`. Its hypotheses are, in order, `Smooth G.X.hom`,
`IsProper G.X.hom`, and `GeometricallyConnected G.X.hom`. For these data it asserts
the existence of

- a natural number `n : ℕ`, including `n = 0`;
- line bundles
  `L : Fin n → Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left`;
- actual global sections
  `s : (i : Fin n) → Langlands.SchemeModule.GlobalSections (L i).obj`;

satisfying the published predicate
`Langlands.AlgebraicGeometry.Picard.IsFinitePointTangentSectionSeed G.X.hom z n L s`,
where
`z = (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X).left`
is the unit of the group scheme. As a morphism in the over category, the unit is
a rational point of the structure morphism `p = G.X.hom`.

The published `LineBundle`, `GlobalSections`, and seed predicate are used unchanged.
In the namespace `Langlands.AlgebraicGeometry.Picard`, the seed predicate has four
clauses:

1. Every `s i` vanishes along `z`.
2. For every `i`, there is a rational point `y` at which `s i` does not vanish.
3. For every rational point `x ≠ z`, some `s i` does not vanish along `x`.
4. For every nonzero rational tangent vector `t` at `z`, some `s i` does not
   vanish along `t`.

Here a rational point is a section of `p`, namely a morphism `x : Spec K ⟶ G.X.left`
with `x ≫ p = 𝟙`. Vanishing along a morphism means that the pullback of the global
section is zero. A rational tangent vector is a morphism
`t : Spec K[ε] ⟶ G.X.left` over `K`, restricting to `z` under `ε ↦ 0`;
`K[ε]` is `DualNumber K`. It is nonzero when it differs from the constant
`K[ε]`-point at `z`. These notions are the unchanged published definitions in
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`.

## Original source and derived formulation

The source is J. S. Milne, *Abelian Varieties*, corrected author version January 2,
2022, proof of Theorem 7.1, [p.11](https://www.jmilne.org/math/xnotes/AVs.pdf#page=11).
The registered source is `milne-abelian-varieties-1986-author-2022`, retained at
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`,
SHA256 `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Pages 2–3 and 11 were read directly for this statement.

In the first step, Milne asserts the existence of a finite set `{Zᵢ}` of prime
divisors through `0` such that (a) `⋂ Zᵢ = {0}` and (b) no nonzero tangent vector
at `0` lies in every `T₀(Zᵢ)`. The printed (b) writes `tᵢ ∉ T₀(Zᵢ)`; the subscript
is a misprint for the fixed vector `t`. The vector must be nonzero, since the zero
vector belongs to every tangent space.

This statement has derived, internal provenance. It expresses Milne's existence
claim through the section formulation of the published seed predicate:
each `Zᵢ` is replaced by a line bundle and a global section, intended in Milne's
argument to be `L(Zᵢ)` and its canonical section. Property (a) gives clauses 1
and 3, with points tested only on rational points. Over an algebraically closed
field and for a scheme of finite type, closed points are rational points.
Property (b), interpreted through dual-number points and pullback vanishing,
gives clause 4. Clause 2 records that each zero set is a proper subset by
requiring a rational point outside it; a prime divisor is a proper subset.
This use of “proper” concerns subsets, distinct from the properness hypothesis
on the structure morphism.

No comparison with prime or Cartier divisors is proved here. In particular,
this module proves no correspondence of zero loci with closed subsets or of
dual-number vanishing with tangent spaces. Producing these sections from prime
divisors needs local factoriality of smooth schemes. The statement neither
adds local factoriality as a hypothesis nor discharges that geometric obligation.

The retained [author errata](https://www.jmilne.org/math/articles/1986b.html)
were read in full before the PDF. They are registered as
`milne-abelian-varieties-1986-errata-2026-10-25`, retained at
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`,
SHA256 `e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`.
They say that the listed corrections are incorporated in the xnotes version;
none concerns Section 6 or 7. No source-specific project errata note was found.

## Hypotheses and dimension zero

Milne works over an algebraically closed field with an abelian variety, defined
as a complete connected group variety (p.3, with the variety conventions on p.2).
The Lean statement uses a commutative group scheme with smooth, proper and
geometrically connected structure morphism. It proves no bridge between these
presentations. Commutativity is an extra hypothesis retained to match the parent
`Langlands.GroupScheme.AlgebraicallyClosedSeparatingLineBundleStatement` and its
assembly interface; Milne's first step does not use it. The statement covers
every characteristic and arbitrary `u`.

Allowing `n = 0` is essential. A smooth proper geometrically connected group
scheme of dimension zero over an algebraically closed field is isomorphic over
`K` to `Spec K` (a standard fact, not formalized here). Every rational point is
then the unit and there is no nonzero rational tangent vector at the unit.
The empty family satisfies the seed conditions. No nonempty family can do so:
clause 1 forces every section to vanish at the unit, while clause 2 would
require a rational point, necessarily the unit, where that section does not
vanish. This is the case explained in the `n = 0` section of the published
`Langlands/AlgebraicGeometry/Picard/FiniteSectionSeed.md`.

## Proof scope

The target has no outer assumption of a dimension bound, projectivity,
ampleness, regularity, factoriality, supplied divisors, supplied line bundles,
or a comparison certificate. Its planned proof must construct actual sections
without using projectivity, ample existence, or their consequences. The
divisor-to-section comparisons and existence proof remain separate work.
This module adds no axiom and proves no existence theorem.
