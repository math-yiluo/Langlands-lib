# Open charts of actual induced rational spectra

Worker 36 derives this chart package from the published balanced quotient,
generic coset-copy homeomorphism, and rational-spectrum transport constructions.
The carriers are the actual rational closed-ideal Tate quotients' spectra.

## Hypotheses and charts

The hypotheses are those of `InducedRationalSpectrum`: a complete ultrametric
normed field `K`, a presented strict affinoid algebra `P`, a topological group
`G`, and a `RationalSpectralAction G P`. The universes of `K` and `G` remain
independent. An object `X` retains its actual open subgroup `H` and an
`H`-invariant rational presentation. Its `LocalSpectrum` is the published actual
Banach spectrum of that presentation's rational quotient algebra, with the
constructed inverse-pullback subgroup action. Its `InducedSpectrum` is the
published balanced quotient `G ×_H X.LocalSpectrum` with quotient topology.

`X.inducedChart a` is the continuous map `x ↦ [a,x]`.
`X.inducedComponent` is the continuous map `[a,x] ↦ aH` to the left-coset
quotient with its quotient topology. Applying the published generic chart
theorems proves that each chart is an open embedding, its image is the fiber
of the component map at `aH`, that image is clopen, and the chart images cover.
The subgroup's stored openness supplies the only openness hypothesis. The
identity chart is the previously constructed `inducedUnit`.

`X.inducedChartDomain a` is the actual open subset given by this image.
`mem_inducedChartDomain_iff` identifies its points by their component.
`X.inducedChartHomeomorph a` is the homeomorphism from the actual rational
quotient spectrum onto that open subset, obtained from the proved embedding.
Its composite with the subtype inclusion is exactly `inducedChart a`.

The representative-change formula is

`inducedChart (a*h) x = inducedChart a (h • x)`.

The subgroup action on the right is the existing action constructed from the
bounded section automorphisms. The ambient structural map has the formula

`ambientMap (inducedChart a x) = a • localToAmbient x`.

Both identities specialize the already proved balanced-quotient formulas.
No assertion about an analytic structure on these open subsets is needed.

## Coset copies

`X.InducedCosetCopies` is the actual dependent sum

`Σ c : G/H, X.LocalSpectrum`,

with its sum topology. The homeomorphism `X.inducedCosetHomeomorph` maps
`(c,x)` to `[c.out,x]`. It specializes the generic homeomorphism, whose
continuity and inverse continuity have already been proved. Its component is
`c`. If `a*c.out = d.out*h`, the full group action in these coordinates is

`a • inducedCosetHomeomorph (c,x) = inducedCosetHomeomorph (d,h • x)`.

The chosen representative of the identity coset need not be `1`; the
distinguished identity chart remains `inducedChart 1`.

## Transport in charts and coset coordinates

Let `f : X ⟶ Y` have label `l`, source subgroup `H` and target subgroup `J`.
The imported arrow carries `l*H*l⁻¹ ≤ J` and the constructed subgroup map
`h ↦ l*h*l⁻¹`. `Hom.cosetMap f` descends

`aH ↦ (a*l⁻¹)J`.

To prove this is well defined, equality of source cosets gives
`a⁻¹*b ∈ H`. Its image under the actual subgroup homomorphism belongs to `J`;
this is exactly
`(a*l⁻¹)⁻¹*(b*l⁻¹) ∈ J`. Continuity follows by descent from the continuous
map on group representatives. Quotient induction proves the identity and
composition laws, using the composite label `g.label*f.label`.

The component triangle is proved by quotient induction:

`Y.inducedComponent (f.inducedMap z) = f.cosetMap (X.inducedComponent z)`.

The imported induced-map formula gives the chart formula

`f.inducedMap (X.inducedChart a x)
  = Y.inducedChart (a*l⁻¹) (f.localSpectrumMap x)`.

Here `f.localSpectrumMap` is comap by the actual bounded rational pullback
`f.restriction`; it is not an assumed continuous map. The chart formula proves
that transport maps the entire source chart domain into the indicated target
domain. `Hom.chartRestriction` corestricts the actual continuous induced map
to those subsets. `chartRestriction_inducedChartHomeomorph` proves that the
restriction, expressed through the two chart homeomorphisms, is precisely
`f.localSpectrumMap`.

`Hom.inducedCoordinates f` conjugates the actual continuous induced map by
the source and target coset-copy homeomorphisms. It is continuous by
composition. The proved component triangle identifies its first coordinate
as `f.cosetMap`. If

`c.out*l⁻¹ = d.out*h`, with `h ∈ J`,

then `inducedCoordinates_apply_of_eq` proves the full formula

`f.inducedCoordinates (c,x) = (d,h • f.localSpectrumMap x)`.

The proof applies the target homeomorphism's injectivity, expands the
induced-map formula and uses the balancing identity. The pointwise identity
and composition laws for these coordinate maps follow from those for
`inducedMap` and cancellation of the middle homeomorphism and its inverse.

## Provenance and scope

This is derived underlying topological infrastructure. The constructions and
their proofs specialize and combine the published modules
`InducedRationalSpectrum` and `Topology.GroupAction.InducedCharts`; the coset
map, chart restrictions and coordinate transport formulas are derived here.
No nonempty spectrum, finite-index subgroup, faithful action, reduced algebra,
or separation hypothesis is introduced.

The original motivation and action convention are Berkovich's unfinished
*Etale equivariant sheaves on p-adic analytic spaces* (1995–1996), retained
`Equish_1996` manuscript, Construction 1.1.2, printed/PDF p. 2. It constructs
the disjoint union of copies indexed by left cosets of an open subgroup and
defines the action from `g*gi = gj*h`. The raw-labelled rational transport
formulas and their inverse-label correction are derived from the existing
bounded rational pullbacks, rather than quoted as a statement of that
manuscript.

The registered source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf* has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The original construction was reread for this contribution. The registered
source is an unfinished manuscript. No source-specific errata note was
present in the current Library.

The package constructs topological charts on actual rational spectra and
their transport maps. The term “chart domain” here denotes the explicitly
constructed open subset of the induced topological space. Analytic atlases,
structure-sheaf descent, analytic morphisms, etale and quasi-etale sites,
induction in stages, and the Harris tower specialization remain further
obligations.
