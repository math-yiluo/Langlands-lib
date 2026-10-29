# Bounded transport in compatible induced rational charts

Author: Worker 36.

This derived construction supplies actual bounded algebra pullbacks for the
published induced rational spectra in arbitrary compatible source and target
charts. It proves algebraic compatibility with chart changes and composition
and realizes the resulting spectrum maps on the actual balanced quotient.

The field `K` is a complete ultrametric normed field. The ambient algebra `P`
is a presented strict affinoid algebra, constructed as a finite Tate algebra
modulo a closed ideal. The topological group `G` acts through the published
`RationalSpectralAction G P`. An object `X` stores an actual open subgroup
`H_X` preserving a rational locus. Write `A_X` for its constructed rational
quotient algebra and `q_X : P → A_X` for its bounded base map. Its actual
spectrum is `X.LocalSpectrum`, and its induced space is the balanced quotient
of `G × X.LocalSpectrum`. The field and group have independent universes.

## Construction and uniqueness

A transport arrow `f : X ⟶ Y` retains a group label `l = f.label`, a
conjugation inclusion of the open subgroups, and the assertion that `l` maps the
source rational locus into the target rational locus. The published rational
extension construction gives the actual bounded pullback
`f.restriction : A_Y → A_X`, with
`f.restriction ∘ q_Y = q_X ∘ ρ(l).inv`.

Let `a,b ∈ G` satisfy the compatibility condition
`b H_Y = (a l⁻¹) H_Y`. The target subgroup element comparing these
representatives is `h = b⁻¹ a l⁻¹`.
`chartPullback f a b hab` is the composite

`f.restriction ∘ chartAlgebraChange_Y(b, a l⁻¹).hom`.

The second factor is the already constructed inverse section operator at `h`.
Thus this is an actual bounded `K`-algebra homomorphism `A_Y → A_X`, with no
new representing algebra or section action assumed.
`chartPullback_comp_baseMap` proves

`chartPullback(f,a,b) ∘ q_Y = q_X ∘ ρ(b⁻¹ a).inv`.

The proof composes the two existing base-map triangles. The inverse ambient
operators compose in reverse group order, and `h l = b⁻¹ a` cancels the
transport label. The private helper `ambientInv_comp` records this inverse
composition convention. `chartPullback_unique` applies rational base-map
extensionality for the target rational quotient. Every bounded homomorphism
with this triangle equals the constructed map. This uses the rational
extension property rather than separation of algebra elements by spectral
points.

## Realization on spectrum points

`chartSpectrumMap f a b hab` is the actual continuous comap of
`chartPullback` on the quotient spectra. `chartSpectrumMap_apply` identifies it,
definitionally, with target coordinate change from `a l⁻¹` to `b` after
`f.localSpectrumMap`. The chart-change realization and the published transport
formula then give `inducedChart_chartSpectrumMap`:

`chart_Y(b, chartSpectrumMap(f,a,b,x)) = f.inducedMap(chart_X(a,x))`.

`chartSpectrumMap_unique` uses injectivity of the actual open target chart to
prove uniqueness of this coordinate. No nonemptiness or finite-index
assumption is needed. All continuous maps use the actual inherited spectrum
and quotient topologies.

`chartPullback_canonical` recovers `f.restriction` when `b = a l⁻¹`,
because the target chart change is the identity.
`chartSpectrumMap_canonical` recovers `f.localSpectrumMap` in those charts.

## Identity, composition and representative changes

`chartPullback_id` identifies the identity arrow's pullback in chart `a` with
the actual bounded identity on `A_X`. It applies the base-map uniqueness
theorem, `a⁻¹ a = 1`, and preservation of `1` by `ρ`.
`chartSpectrumMap_id` follows from point-coordinate uniqueness and the
published identity law for the induced map.

For `f : X ⟶ Y` and `g : Y ⟶ Z`, suppose `a,b` are compatible for `f`
and `b,c` are compatible for `g`. `chartCoset_comp` proves compatibility of
`a,c` for `f ≫ g`: it applies `g.cosetMap` to the first coset equality and
uses `(f ≫ g).label = g.label * f.label`.
For any proof of the resulting compatibility, `chartPullback_comp` states

`chartPullback(f ≫ g,a,c) = chartPullback(f,a,b) ∘ chartPullback(g,b,c)`.

Its proof applies bounded base-map uniqueness to the right side and simplifies
`(c⁻¹ b)(b⁻¹ a) = c⁻¹ a`. `chartSpectrumMap_comp` proves the corresponding
covariant point composition by applying the injective chart at `c`, realizing
both maps on the induced quotient, and using its composition law.

Suppose `a H_X = a' H_X` and `b H_Y = b' H_Y`.
`chartCoset_change` derives compatibility of `a',b'` from that of `a,b` by
applying `f.cosetMap` to the source coset equality.
With `D_X(a,a')` and `D_Y(b,b')` denoting the bounded chart-change
homomorphisms, `chartPullback_naturality` proves

`D_X(a,a') ∘ chartPullback(f,a,b) = chartPullback(f,a',b') ∘ D_Y(b,b')`.

Rational base-map extensionality reduces both sides to the same map
`q_X ∘ ρ(b⁻¹ a').inv`. This proves equality of actual bounded algebra
maps. `chartSpectrumMap_naturality` gives the corresponding point-coordinate
square. Its implemented proof uses target chart injectivity and the two
chart realizations.

## Chosen coset coordinates

For `c : G/H_X`, `cosetChart_compatible` compares the quotient's chosen
representatives `c.out` and `(f.cosetMap c).out` using `Quotient.out_eq`.
`cosetChartPullback` specializes the constructed bounded pullback to those
representatives; `cosetChartPullback_comp_baseMap` records its actual base
triangle. `cosetChartSpectrumMap` is the corresponding continuous spectrum map.

`inducedCoordinates_apply` gives the exact sigma-coordinate formula

`f.inducedCoordinates ⟨c,x⟩ = ⟨f.cosetMap c, f.cosetChartSpectrumMap c x⟩`.

The proof applies injectivity of the published coset-copy homeomorphism and
the chart realization above. It supplies the previously missing coordinate
map without requiring the caller to choose a subgroup element or an equation
comparing representatives.

## Provenance and scope

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
§1.2, Definition 1.2.3 and Remark 1.2.4(i), printed p.16 / PDF p.13, requires
bounded affinoid-atlas restrictions and records their composition.
Definition 1.2.7, printed p.18 / PDF p.15, requires compatible affinoid maps in
all pairs of atlas charts containing the image. These passages motivate the
bounded chart compatibility constructed here. Registered source
`berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, unfinished
1995–1996 manuscript, Construction 1.1.2, printed/PDF p.2, supplies the
left-coset-copy and subgroup coordinate convention. Registered folder source
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member PDF
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Both original passages were read, and no source-specific errata file was
present in the workspace, Library or shared notes when checked.
The new pullbacks, uniqueness, naturality, composition and exact coordinate
formula are internal deductions from published rational extension maps,
bounded chart changes and the balanced quotient construction.

This unit does not establish the affinoid-domain universal properties of a
general atlas, refinement or gluing, structure-sheaf descent, the analytic
morphism category, étale or quasi-étale sites, equivariant analytic sites, or
the Harris tower specialization. In particular, it does not declare its
induced maps to be strong analytic morphisms in Definition 1.2.7.
The action remains continuous for the restricted rational spectral topology
specified in `RationalSpectralAction` (defined in `SpectralAction.lean`);
comparison with the full analytic automorphism topology remains separate.
