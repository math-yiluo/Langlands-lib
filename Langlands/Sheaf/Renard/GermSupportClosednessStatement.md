# Renard II.2.2: local vanishing and relative support closedness

Worker 633 authored these statement definitions. Worker 6 supplied the
original-source audit, focused interface specification and intended local
vanishing route.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.2, printed p.37 /
one-based PDF p.43: the support definition, proposition and its proof. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF pp.43–44 were read in full; the beginning of printed p.38 / PDF p.44
places the later compact-section definition outside this statement unit.

The supplementary 2010-edition *Corrections et compléments*, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF pp.2–3. These pages correct preceding cover-index,
adjunction and disjoint-union formulas; they do not change this support
proposition. The 2026 original remains the governing edition.

The source assumes a sheaf on a chosen basis and regards its sections as
locally represented families of stalk values. It defines support by
nonzero values, without taking a closure, and asserts that this set is
closed **in the section's domain open**. The imported
`Langlands.Sheaf.Renard.GermSupport` realizes that definition on the original
`GermSections F U` carrier:

```text
germSupport s : Set U = {x | s.val x ≠ 0}.
```

The imported stalks, locally represented families, and pointwise section
values are used unchanged. This module adds four `Prop`-valued declarations
and a closed aggregate. It proves none of the asserted propositions.

`RawGermLocalVanishingStatement F` quantifies every actual `U : Opens X`,
section `s : GermSections F U` and point `x : U`. If `s.val x = 0`, it
asserts the existence of `V : BasisOpen B`, a membership witness
`x.val ∈ V.obj`, and an actual inclusion `hVU : V.obj ≤ U`, with

```text
∀ (y : X) (hy : y ∈ V.obj), s.val ⟨y, hVU hy⟩ = 0.
```

Thus the original section vanishes at every point of one whole contained
basis neighborhood. The interface includes the containment and the actual
membership proofs needed to evaluate the same section; it asserts more
than vanishing only at the chosen point.

This explicit neighborhood conclusion records the intermediate conclusion
of the source proof. Its mathematical route first uses the original
section's local representability near `x` to obtain a representative
`t : Sections F W` on a contained basis open `W`. The zero value at `x`
means that this representative has zero original germ there. The original
stalk representative relation supplies a smaller basis neighborhood `V`
of `x` on which the restriction of `t` is zero. Compatibility of the
original germ maps with restriction then gives zero values of `s` at
every point of `V`. This explains the statement's provenance and
hypotheses; the route is not implemented as a proof in this module.

`RawGermRelativeSupportClosednessStatement F` quantifies every actual open
and every original germ section and asserts precisely
`IsClosed (germSupport s)`. Lean uses the subtype topology on `U` for this
predicate. The intended deduction from local vanishing makes the relative
zero locus open. It does not assert that `germSupportAmbient s : Set X`
is closed in `X` for arbitrary open `U`.

Both raw statements accept an arbitrary `RawPresheaf.{u,v} B`.
Dropping the source's sheaf input is an internal strengthening: the local
argument uses local representability and the stalk representative relation,
and does not infer equality of original sections from their germs on a
whole domain. In particular it needs no sheaf separation axiom. The
explicit local-neighborhood declaration is internal interface packaging of
the source proof, rather than an additional separately stated proposition
in the book.

`NormalizedGermLocalVanishingStatement F` and
`NormalizedGermRelativeSupportClosednessStatement F` are abbreviations
specializing the respective raw statements to exactly `F.obj` for
`F : Presheaf.{u,v} B`. Their sections are therefore exactly
`GermSections F.obj U`, and their support is the same published
`germSupport`. Normalization introduces no change of carriers, stalks or
topologies and no comparison hypothesis. Even these normalized
specializations do not require a sheaf condition.

`GermSupportClosednessStatement.{u,v}` is the closed conjunction of the
four families, in the order raw local vanishing, raw relative closedness,
normalized local vanishing, and normalized relative closedness. It
quantifies `X : Type u`, its supplied topology, the arbitrary chosen
`B : OpenBasis X`, every raw or normalized presheaf, every domain open,
and all sections and points required by the individual assertions.
Its full declaration returns `Prop` with no free object parameters.
The original section universe `v` is independent of the space universe
`u`; the imported section carrier retains `Type (max u v)`.

There is no additional separation, Hausdorffness, local compactness, total
disconnectedness, intersection-closure, nonempty-domain or nonzero-stalk
hypothesis. The basis need not contain the empty open. Empty spaces and
all empty actual domain cases remain included; local vanishing on an empty
domain has no point to quantify.

The exact proof of the published aggregate, compact-section additive
structures and maps, arbitrary-open compact restriction issues,
original-section support comparisons, canonical-unit invertibility,
clopen zero extension and II.2.4 exhaustion remain separate units.
This statement family does not complete II.2.2.
