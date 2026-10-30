# Bounded full-group action on the actual induced affinoid atlas

Author: Worker 36.

This module constructs the full-group action by bounded morphisms of the
actual induced quotient-algebra family. Its spectrum realization agrees
with the existing action on the balanced quotient and is jointly
continuous. It supplies compatible bounded pullbacks for every admissible
pair of charts in the constructed disjoint affinoid atlas.

## Sources and provenance

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces*, retained Equish_1996 manuscript (1995–1996), Construction 1.1.2,
printed/PDF page 2, constructs induction from an open subgroup using
left-coset copies. If `g*gi = gj*h`, its action from copy `i` to copy `j`
is the subgroup operator `h` in those coordinates. This module constructs
that rule on the actual bounded chart algebras of the rational-spectrum
specialization. Registered folder source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf* has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The discussion on printed/PDF pages 1–2 defines continuity using a topology
on analytic automorphisms tested on compact domains and functions. The
joint spectral continuity proved here has the narrower scope below.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
section 1.2, Definition 1.2.7 and the subsequent composition discussion,
printed page 18 / PDF page 15, requires compatible affinoid morphisms for
every chart pair with the required containment. The present disjoint
atlases permit these maps and their coherence to be constructed directly.
Registered source: `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The rendered original confirms printed page 18; text extraction misreads
its page header.

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
Definition 2.1.11, printed/PDF page 8, defines affinoid spaces as the
category dual to affinoid algebras with bounded homomorphisms. This fixes
the contravariant pullback order. Registered source:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

These original passages were read; the formula and page numbers were
checked on rendered pages. No source-specific errata note was present in
the workspace, current Library or shared project notes. All constructions
and coherence proofs below are derived from the published rational
section action, strict/generalized comparison, balanced quotient and
induced atlas. They are not separately numbered results in the sources.

## Hypotheses and actual algebras

Work in
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport`.
Let `K : Type u` be a complete ultrametric normed field, `P` a presented
strict affinoid algebra, `G : Type v` a topological group,
`ρ : RationalSpectralAction G P`, and `X : ρ.OpenSubgroupTransport`.
The universes `u` and `v` are independent. Write `H = X.subgroup`,
`A = X.domain.obj.algebra` and `B = X.inducedChartAlgebra`.

Here `A` is the actual strict rational closed-ideal Tate quotient and
`B = PresentedAffinoidAlgebra.ofStrict K A` is its actual positive-polyradius
quotient presentation with radii one. The published bounded equivalence
`E = PresentedAffinoidAlgebra.strictEquiv K A : B ≃ A` compares those
quotients. The object `X.inducedAffinoidObject` has index type `G/H` and
constant algebra family `B`. Its space is the actual topological sum of
`BanachSpectrum B`. The published `X.inducedAffinoidHomeomorph` identifies
it with `X.InducedSpectrum`, the actual balanced quotient
`G ×_H X.LocalSpectrum`. Its atlas retains precisely the nonempty
component spectra.

## Representative correction and bounded action

For `c : G/H`, the definition `actionChartElement g c` constructs

`δ(g,c) = (g • c).out⁻¹ * (g * c.out) : H`.

Its membership proof uses equality of the two cosets. The statements
`actionChartElement_coe` and `actionChartElement_spec` give the ambient
group formula and `g*c.out = (g • c).out*δ(g,c)`. The latter is exactly
the representative equation used in Construction 1.1.2. The proofs
`actionChartElement_one` and `actionChartElement_mul` use group
cancellation to establish

`δ(1,c) = 1`, and
`δ(g*h,c) = δ(g,h • c) * δ(h,c)`.

There is no normalization assumption on the chosen representative of
the identity coset.

The published `X.chartSectionAction : H →* BoundedAlgAut K A` is the
forward section action. The point action is its inverse pullback.
Accordingly `strictActionPullback g c` is

`(X.chartSectionAction (δ(g,c)))⁻¹.hom : A → A`.

`strictActionPullback_one` and `strictActionPullback_mul` prove identity
and contravariant composition as equalities of bounded algebra maps.
The multiplication proof applies the cocycle, multiplicativity of the
section action and the inverse-of-product identity.

`affinoidActionPullback g c : B → B` applies the published
`PresentedAffinoidAlgebra.ofStrictMap K` to this map. Concretely it is
`E.symm ∘ strictActionPullback(g,c) ∘ E`.
The identity and composition laws of the published `ofStrictFunctor`
give `affinoidActionPullback_one` and `affinoidActionPullback_mul`:

`β(1,c) = id`, and
`β(g*h,c) = β(h,c) ∘ β(g,h • c)`.

`affinoidActionMap g` is the family morphism with component function
`c ↦ g • c` and bounded pullback `β(g,c)`. The proofs
`affinoidActionMap_one` and `affinoidActionMap_mul` combine the index
and algebra equalities using `AffinoidFamily.Hom.ext`. In particular,

`affinoidActionMap (g*h) = affinoidActionMap h ≫ affinoidActionMap g`.

This is the multiplication convention of categorical endomorphisms.
The selected definition `inducedAffinoidAction` packages these maps as
an `Action (AffinoidFamily.{u,v} K) G` on `X.inducedAffinoidObject`.
`inducedAffinoidAutomorphisms` is the resulting group homomorphism into
its categorical automorphisms; the inverse is the map for `g⁻¹`.

## Realization and joint continuity

`strictActionPullback_spectrum` identifies its spectrum comap with
`δ(g,c) • x` on the actual strict rational spectrum.
`affinoidActionPullback_spectrum` proves that the generalized quotient
comparison intertwines this map:

```text
localAffinoidSpectrumHomeomorph.symm (comap β(g,c) x)
  = δ(g,c) • localAffinoidSpectrumHomeomorph.symm x.
```

The proof evaluates seminorms on each algebra element and cancels the
actual equivalence with its inverse. For every point `p` of the actual
family space, `affinoidActionMap_realization` then proves

```text
g • X.inducedAffinoidHomeomorph p
  = X.inducedAffinoidHomeomorph
      ((X.affinoidActionMap g).spectrumMap p).
```

It decomposes `p` into a coset and a spectrum point, applies the
published balanced-quotient chart action with the representative equation,
and uses the spectrum comparison. `inducedAffinoidSpectrumIso` packages
this homeomorphism and equivariance as an isomorphism of `TopCat`
actions between the spectrum functor applied to `inducedAffinoidAction`
and the published `inducedSpectrumAction`.

`continuous_affinoidAction` writes the action on actual family spectra
as the conjugate of the existing jointly continuous balanced-quotient
action by `X.inducedAffinoidHomeomorph`. Continuity of the two directions
of this homeomorphism proves joint continuity on
`G × X.inducedAffinoidObject.Space`. The definition
`inducedAffinoidContinuousSpectrum` packages that action as a
`ContAction TopCat.{max u v} G`.

## Every admissible atlas chart pair

`actionAtlasTarget g c` uses the actual family map's `chartTarget`.
The target chart is nonempty because a seminorm from the nonempty source
chart comaps along its bounded pullback. Its index is `g • c.val`;
`actionAtlasTarget_one` and `actionAtlasTarget_mul` prove the index
unit and action laws. `image_actionAtlasChart_subset` proves containment
of the image of chart `c` in this target chart by the realization formula.

For any chart `d` and containment

`h : (fun z => g • z) '' range (chart c) ⊆ range (chart d)`,

`actionAtlasTarget_eq g c d h` proves `actionAtlasTarget g c = d`.
It transfers the containment through the actual homeomorphism and uses
the published uniqueness of a target nonempty disjoint component.

`actionAtlasPullback g c d h` is `β(g,c.val)`, with type

`BoundedAlgHom K (X.inducedAffinoidAtlas.algebra d)
  (X.inducedAffinoidAtlas.algebra c)`.

Both algebras are literally `B`, so this definition needs no transport
of algebra types. The containment identifies the target index in
`actionAtlasPullback_chart`, which proves

`chart d (comap (actionAtlasPullback g c d h) x) = g • chart c x`.

`actionAtlasPullback_naturality` proves compatibility with restrictions
in both copies of the atlas. If `c ⊆ c'`, `d ⊆ d'` and both action
pairs are admissible, the equation is

```text
restriction(c,c') ∘ actionAtlasPullback(g,c',d')
  = actionAtlasPullback(g,c,d) ∘ restriction(d,d').
```

Its proof rewrites the published restrictions as bounded identities and
identifies `c = c'` using nonempty-component containment. The unit result
`actionAtlasPullback_one` is the bounded identity on the same chart.
For every compatible triple `c,d,e`, `actionAtlasPullback_mul` proves

`actionAtlasPullback(g*h,c,e) =
  actionAtlasPullback(h,c,d) ∘ actionAtlasPullback(g,d,e)`.

It first identifies `d.val = h • c.val` by containment and then applies
the bounded algebra multiplication law. None of the algebra coherence
proofs infers equality of algebra maps from equality on spectrum points.

## Scope

Empty local spectra and infinite coset sets are permitted. The result
constructs a categorical action by actual bounded family morphisms and
all admissible chart-pair maps for these particular atlases. The inherited
`RationalSpectralAction` has the restricted rational spectral topology
described in `SpectralAction.lean`. The joint continuity result concerns
the realized spectrum action; this module does not construct the full
analytic automorphism topology or compare continuity with it.

Bounded equivariance of transport arrows, general strong-morphism
localization and overlapping atlas gluing, structure sheaves, etale and
quasi-etale sites, the full analytic induction universal property and
Harris's tower specialization remain separate obligations.
