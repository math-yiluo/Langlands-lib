# Radius restriction of relative closed-equation quotients

This module constructs bounded radius restriction for actual relative weighted
series quotients, its continuous contravariant maps on spectra and equation loci,
and compatibility with coefficient transport. The constructions use the
published weighted series, closed-ideal quotient and spectrum interfaces.

## Series restriction over a common field

In `Langlands.Analytic.GeneralizedTateAlgebra`, let `K` be a normed field, let
`A` be an ultrametric normed commutative `K`-algebra, and let `s` and `t` be positive
polyradii on any index type, with `hts : ∀ j, t j ≤ s j`. The existing
`restrictRadius` retains the formal coefficients and defines an `A`-algebra map

\[
\rho_{s,t}:A\{s^{-1}T\}\longrightarrow A\{t^{-1}T\},
\qquad \|\rho_{s,t}(f)\|_t\leq\|f\|_s.
\]

`restrictRadiusAlgHom` restricts its scalar field to `K` and bundles the same
map with bound one. Its application lemma identifies it with `restrictRadius`.
The norm bound, constant-series and variable formulas, and identity and
composition laws follow from the existing radius restriction. The proof of
`restrictRadiusAlgHom_mapCoefficients` observes that coefficient transport and
radius restriction give exactly the same formal coefficients in either order.
The coefficient map may be any bounded `K`-algebra map between two such
ultrametric normed commutative algebras.

## Compatible equations and actual quotient maps

The remaining declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRelations`.
Let `K` have ultrametric distance, let `A : PresentedAffinoidAlgebra K`, and let
`s,t : PositivePolyradius (Fin m)` satisfy the same coordinatewise inequality.
For arbitrary sets of relative series `E` at radius `s` and `F` at radius `t`,
write

\[
I_{s,E}=\overline{\operatorname{span}_{\mathrm{ideal}}(E)},\qquad
Q_{s,E}=A\{s^{-1}T\}/I_{s,E}.
\]

The closed ideal, quotient carrier and quotient norm are the imported
`ideal K A s E` and `QuotientAlgebra K A s E`. In particular, `A` itself is the
actual presented weighted-series quotient supplied by the Library.

`RadiusMapsRelations K A s t hts E F` is the proposition

\[
\forall f\in E,\quad \rho_{s,t}(f)\in I_{t,F}.
\]

`radiusMapsRelations_of_mapsTo` supplies this compatibility if restriction sends
the source equations into the target equations. Membership in the target closed
ideal is the general hypothesis. `radiusMapsRelations_ideal` extends it to the
entire source closed ideal: the composite of restriction with the target quotient
projection annihilates the generators, so the published `annihilates_ideal`
theorem applies to their closed ideal. Compatibility holds for equal radii and
the same equation set and composes for `q ≤ t ≤ s`.

`radiusMap` uses the published `descend` to construct

\[
\overline{\rho}_{s,t}:Q_{s,E}\longrightarrow Q_{t,F}
\]

as a `BoundedAlgHom K`. Its representative formula is

\[
\overline{\rho}_{s,t}(\overline f)=\overline{\rho_{s,t}(f)}.
\]

`radiusMap_comp_quotientMap` gives the same assertion as an equality of bundled
algebra maps. The map preserves the image of each coefficient `a : A` and the
image of each new coordinate. `norm_radiusMap_le` proves contraction for the
actual quotient norms. The series restriction and the target quotient projection
are contractive, and the published quotient norm descent theorem retains the
constant one. No isometry or injectivity of the quotient map is asserted.

`eq_radiusMap` proves uniqueness from the representative formula, using
surjectivity of the source quotient projection. The identity and composition
laws `radiusMap_self` and `radiusMap_trans` use the same extensionality and the
corresponding series restriction laws. The composition law permits any three
equation sets satisfying the two compatibility conditions.

## Spectra and equation loci

`radiusSpectrumMap` is the continuous pullback

\[
\overline{\rho}_{s,t}^{\,*}:
\mathcal M(Q_{t,F})\longrightarrow\mathcal M(Q_{s,E}).
\]

For `x` in the target quotient's spectrum it evaluates an element `a` as
`x (radiusMap ... a)`. The representative, coefficient and coordinate formulas
follow from the corresponding algebra map formulas. Its identity and
contravariant composition laws are equalities of bundled continuous maps.
They are proved by spectrum extensionality and `radiusMap_self` or
`radiusMap_trans`.

Recall the published common equation locus

\[
Z_{s,E}=\{x\in\mathcal M(A\{s^{-1}T\}):\forall f\in E,\ x(f)=0\}.
\]

`equationLocusRadiusMap` restricts the continuous spectrum pullback of the series
restriction to `Z_{t,F} → Z_{s,E}`. Its membership proof uses the published
`mem_equationLocus_iff`: a point of `Z_{t,F}` annihilates the whole closed ideal
`I_{t,F}`, which contains every restricted source equation. Its evaluation law is

\[
(\rho_{s,t}^{\,*}x)(f)=x(\rho_{s,t}(f)).
\]

The module proves the corresponding constant and variable laws and identity and
contravariant composition as bundled continuous map equalities.
`spectrumHomeomorph_radius_naturality` proves, pointwise, that

\[
h_{s,E}\bigl(\overline{\rho}_{s,t}^{\,*}x\bigr)
 =\rho_{s,t}^{\,*}\bigl(h_{t,F}(x)\bigr),
\]

where `h` is the published actual quotient-to-equation-locus homeomorphism.
Both sides evaluate a source series by applying `x` to the same restricted
quotient representative.

## Naturality with coefficient transport

Let `B` be another actual presented algebra over `K` and let
`φ : BoundedAlgHom K A B`. Choose equation sets `E,E'` at radius `s` over `A,B`
and `F,F'` at radius `t` over `A,B`, respectively. Assume radius compatibility
for `E → F` and `E' → F'`, and the published `MapsRelations` condition for
`φ` from `E` to `E'` and from `F` to `F'`.

`radiusMap_transport` proves the algebra map square

\[
\overline{\rho}_{B,s,t}\circ\phi_{s,*}
 =\phi_{t,*}\circ\overline{\rho}_{A,s,t}.
\]

Here `φ` acts by the published actual quotient coefficient `transport`.
The proof reduces to representatives and the equality of the two coefficientwise
series maps. `radiusSpectrumMap_spectrumTransport` proves the reversed
commuting square for continuous quotient-spectrum maps by evaluating this
algebra equality. `equationLocusRadiusMap_equationLocusTransport` proves the
same commuting square on the equation loci, directly by the series equality.
These results assume the four stated relation compatibilities; they do not
assume a resulting quotient equality or spectrum identification.

## Scope and provenance

All new radii are arbitrary positive real radii. Empty variable blocks,
empty equation sets, nonproper ideals, zero quotients and trivial valuations
are allowed. Completeness is unnecessary for these normed algebra and spectrum
constructions. Over complete `K`, the relative quotient's completeness is
already provided by the imported construction. This module does not establish
affinoid classification over incomplete fields, arbitrary presentation
independence, a scalar additional-equation comparison, an embedding or
analytic-domain description of the spectrum map, structure sheaves or sites.

The registered original is Vladimir Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), source
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF page 4, Definitions 1.2.3 and 1.2.5 and Exercise 1.2.4, supplies
bounded multiplicative spectra and their evaluation topology. Section 2.1,
page 7, supplies the quotient norm. Definition 2.1.6(i)-(ii), page 8, supplies
the relative weighted restricted-series convention; Definition 2.1.11 there
describes the contravariant affinoid-space category.

The source supplies conventions and motivation. Radius compatibility,
closed-ideal descent, the quotient norm bound, and all functoriality and
naturality laws here are internal consequences of the published actual weighted
series restriction, relative quotient descent, coefficient transport, and
quotient-spectrum constructions. They are not presented as theorems stated
in the cited source definitions.
