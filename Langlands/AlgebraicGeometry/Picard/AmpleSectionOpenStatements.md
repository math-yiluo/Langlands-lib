# Generation opens of sections of powers of an ample line bundle

This module defines two propositions, in universe `u`, in the namespace
`Langlands.AlgebraicGeometry.Picard`. Both are statement targets; this module
provides no proof of either proposition. It imports
`Langlands.AlgebraicGeometry.Picard.Ample` and uses its actual definitions
unchanged.

## Published definitions used by both statements

For an arbitrary scheme `X : Scheme.{u}`, a `LineBundle X` is an actual
locally free rank-one module sheaf. For `L : LineBundle X`:

- `L.IsAmple` means `CompactSpace X` together with the assertion that every
  point lies in the whole generation open of a section of a positive tensor
  power of `L`, and that this whole open is affine. Thus quasi-compactness
  is already part of the ampleness premise.
- `L.powSections n` is
  `Langlands.SchemeModule.GlobalSections
    (Langlands.Scheme.Modules.tensorPow L.obj n)`, the global sections
  `Γ(X, L^{⊗n})`. The published tensor powers are right-associated:
  the zeroth power is the structure module, and the successor power is
  `L.obj ⊗ tensorPow L.obj n`. In particular the first power is presented
  as `L.obj ⊗ 𝒪_X`.
- `L.sectionOpen s` is
  `Langlands.SchemeModule.trivializationOpen (tensorPow L.obj n) s`.
  It is the largest open on which the map from the structure module induced
  by `s` is an isomorphism. It is the whole generation open `X_s`, rather
  than a chosen neighborhood. For line bundles, this is the usual
  residue-field nonvanishing locus. The Library's comparison and rank-one
  results are separate from the present statement definitions.

Both propositions quantify over every scheme and line bundle and have only
`L.IsAmple` as their geometric premise. They add no separatedness,
noetherianity, finite type, base field, or affineness assumption.

## `AmpleSectionOpenBasisStatement`

The full Lean name is
`Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisStatement.{u}`.
For every ample line bundle `L` on `X`, every open `W : X.Opens`, and every
point `x ∈ W`, it asserts that there are a natural number `n` with `1 ≤ n`
and a global section `s : L.powSections n` such that
`x ∈ L.sectionOpen s` and `L.sectionOpen s ≤ W`.
This is the neighborhood formulation of the assertion that the whole
generation opens of positive-power sections form a basis of the topology.

The source is the implication (1) ⇒ (3) of Stacks Project Proposition
28.27.13, tag [01Q3](https://stacks.math.columbia.edu/tag/01Q3); item (3)
is tag [01Q6](https://stacks.math.columbia.edu/tag/01Q6).
In the registered Properties chapter PDF this is Proposition 27.13 on
page 44. The source's homogeneous elements of the positive part of
`Γ_*(X, L)` are sections of some `L^{⊗n}` with `n ≥ 1`. Its explicit
quasi-compactness hypothesis is supplied by `L.IsAmple`.

## `AmpleFiniteSetSectionStatement`

The full Lean name is
`Langlands.AlgebraicGeometry.Picard.AmpleFiniteSetSectionStatement.{u}`.
For every ample line bundle `L` on `X`, every set `E : Set X`, and every
open `W : X.Opens`, it asserts that if `E.Finite` and `E ⊆ (W : Set X)`,
then there are `n : ℕ` with `1 ≤ n` and `s : L.powSections n` such that
`E ⊆ (L.sectionOpen s : Set X)` and `L.sectionOpen s ≤ W`.
The inclusions are non-strict. There is no nonemptiness hypothesis on `E`
or `W`; in particular the empty finite set is included. The exponent is
positive even in this case.

The source is Stacks Project Lemma 28.30.6, tag
[09NV](https://stacks.math.columbia.edu/tag/09NV), Lemma 30.6 on page 51
of the registered Properties chapter PDF. **This proposition is a deliberate
weakening of that lemma:** the source additionally concludes that `X_s` is
affine. Here only `E ⊆ X_s ⊆ W` is retained. The natural-number condition
`1 ≤ n` expresses the source's `n > 0`.

This weakening lets the finite-set assertion be used without first
constructing an affine open containing the finite set, as in source
Lemma 28.30.5. A consumer needing affineness may instead arrange
`W ⊆ U` for an affine open `U` and use the published
`Langlands.AlgebraicGeometry.Picard.affineGenerationLocusIntersection`
on the line bundle corresponding to the tensor power: then
`U ∩ X_s = X_s`. That theorem is separate and is not imported or proved
here. The present module also proves neither the finite-set assertion nor
its deduction from the basis assertion.

## Source and current comments

The primary registered source is
`stacks-properties-chapter-2026-10-28`, The Stacks Project Authors,
*Properties of Schemes*, PDF compiled July 14, 2026,
`literature/Stacks Project — Properties of Schemes chapter (PDF compiled July 14, 2026).pdf`,
SHA256
`2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`.
The exact passages read are pages 44–45 and 51. The current website includes
the chapter number in the displayed proposition and lemma numbers; the
stable tags identify the same statements.

On October 28, 2026, the current statements and comments at tags 01Q3,
01Q6, and 09NV were checked. Retained snapshots are registered as
`stacks-ample-section-opens-comments-2026-10-28`, directory SHA256
`0c9d1abbdd2c77ffdf008fd75650d7b7a71186eacceb963919f34352ddda3a60`,
with files `01Q3.html`, `01Q6.html`, and `09NV.html`. No project errata
note for the primary source was present at that check. The eight comments
on 01Q3 include questions about removing quasi-compactness and discussion
of cohomological criteria; the present statement retains quasi-compactness
through `IsAmple` and makes no cohomological assertion. Tags 01Q6 and 09NV
had no comments. No displayed correction changed either statement used
here.

The Lean statement definitions and initial companion draft were supplied by
Worker 770. Worker 689 checked the original passages, current comments,
and Library correspondence and expanded this companion.
