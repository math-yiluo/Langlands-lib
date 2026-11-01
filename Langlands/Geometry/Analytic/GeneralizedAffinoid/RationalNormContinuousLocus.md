# Rational point continuity and locally constant functions from norm orbits

Author: Worker 56.

This internal construction derives joint continuity on each actual rational
quotient spectrum from norm-continuous base-algebra orbits. It then constructs
open stabilizers of whole locally constant functions in the original parameter
group, and a continuous action on their entire discrete function space.

## Inputs and retained geometry

Let `K : Type u` be a normed ultrametric field and let
`A : PresentedAffinoidAlgebra K` be its actual chosen closed quotient of a
finite positive-polyradius Tate algebra. A chart `d : RationalChart K A`
retains its actual denominator and numerator representatives, arbitrary positive
real radii and unit-generation proof. Its algebra `d.algebra` is the constructed
closed rational quotient, with bounded base map `d.baseMap`. Its locus is
the actual closed rational-inequality subset of `BanachSpectrum A`.

Let `G : Type v` be a topological group, with its given topology, and
`ρ : G →* Aut A`. The hypothesis `hρ` asserts norm-continuity of each
forward algebra-element orbit `g ↦ (ρ g).hom.toAlgHom a`.
The preceding `RationalNormStabilizer` construction derives the full open
subgroup

\[
 H_d=\{g\in G:\rho(g)\cdot d.\mathrm{locus}=d.\mathrm{locus}\},
\]

named `normOpenStabilizer ρ hρ d`. Each subgroup and locus in this module
carries its original subspace topology. Neither a topology on `Aut A` nor
a `DomainSpectralAction` is assumed. The rational locus need not be a
topologically open subset of the ambient spectrum.

All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`.

## Continuous action on the original locus

`normLocusOperator ρ hρ d g` restricts the ambient inverse-pullback action
of `ρ g.val` to `d.locus`. Its membership proof applies the stabilizer's
literal image equality to the original locus point. Continuity for fixed
`g` follows by restricting the continuous pullback along the actual bounded
inverse algebra map. `normLocusOperator_coe` exposes the unchanged ambient
point, and `normLocusAction` bundles these operators as an action of `H_d`.
The identity and multiplication laws are the ambient spectrum action laws,
checked after projecting the subtype.

`continuous_normAmbientSpectrumAction` proves joint continuity of
`(g,x) ↦ ρ(g) • x`. It applies the published
`BanachSpectrum.continuous_comap_of_continuous_apply` theorem to the actual
inverse bounded maps. Their element orbits are continuous because
`ρ(g)⁻¹ = ρ(g⁻¹)` and inversion in `G` is continuous; thus the assumed
forward orbits suffice. This is the same joint-evaluation argument used by
the existing `NormContinuousAction` spectrum construction.

`normLocusAction_isContinuous` composes this ambient joint action with
the continuous inclusions `H_d → G` and `d.locus → BanachSpectrum A`,
then uses the proved locus-membership condition to give a continuous map
into the actual locus subtype. `normLocusContinuousAction` packages the
result as a `ContAction`. These locus declarations do not require coefficient
completeness.

## Continuous action on the actual rational quotient spectrum

The rest of the module assumes `CompleteSpace K`. The actual bounded section
automorphisms `normSectionAction ρ hρ d` then come from the proved full
representation of the rational domain, as constructed in the preceding
module. Their base-map equation implies `normSectionAction_spectrumMap`:

\[
 d.\mathrm{spectrumMap}(\alpha_d(g)\cdot x)
   =\rho(g)\cdot d.\mathrm{spectrumMap}(x).
\]

The proof directly applies
`DomainAutomorphism.stabilizerSectionAction_spectrumMap` to `d.toDomain`
and the constructed stabilizer homomorphism. The published rational
homeomorphism `d.locusHomeomorph` has this same structural map as its
underlying base-spectrum map. Consequently subtype extensionality gives
`normSectionAction_locusHomeomorph`: this homeomorphism intertwines the
actual section spectrum action and `normLocusOperator`.

`normSpectrumAction` uses the inverse bounded maps of these actual section
automorphisms to act on `BanachSpectrum d.algebra`. It is not defined as
an unrelated transported action. `normSpectrumAction_isContinuous` proves
joint continuity by writing its point operator as

\[
 (g,x)\longmapsto
  d.\mathrm{locusHomeomorph}^{-1}
    \bigl(\operatorname{normLocusOperator}(g)
               (d.\mathrm{locusHomeomorph}(x))\bigr).
\]

The inner operator is jointly continuous by the locus theorem, and the two
homeomorphisms are continuous. The equivariance equation and the
homeomorphism's inverse identity identify this composite with the
already constructed bounded-map spectrum action. This uses the proved
rational spectrum identification; no injectivity statement for arbitrary
represented-domain spectrum maps is presumed.

`normSpectrumContinuousAction` bundles the actual action and its proved
joint continuity. Its application lemma gives the exact seminorm formula
`x ((normSectionAction ρ hρ d g).inv.toAlgHom b)`.
This point-continuity result does not assert norm-continuity of the
transported algebra-section orbits.

## All locally constant functions and their stabilizers

Let `C : Type w` be any coefficient set. There is no coefficient topology,
coefficient action or inhabitedness hypothesis. For every
`f : LocallyConstant (BanachSpectrum d.algebra) C`,
`normSpectrumFunctionStabilizer` applies the published
`CompactAction.openStabilizer` theorem to the actual compact rational
quotient spectrum and its newly proved joint `H_d` action.
`mem_normSpectrumFunctionStabilizer` is precisely

\[
 g\in\operatorname{Stab}(f)
 \quad\Longleftrightarrow\quad
 \forall x,\ f(\alpha_d(g)\cdot x)=f(x).
\]

The imported compact-action theorem makes local constancy uniform near the
identity by compactness. It derives openness of this full function stabilizer,
with no fixedness supplied as input.

`normSpectrumLocallyConstantAction` applies the published
`DiscreteLocallyConstant.continuousAction` construction. Its underlying
set contains every locally constant function on the actual spectrum; the
wrapper gives that function set the discrete topology.
`normSpectrumLocallyConstantAction_apply` exposes inverse precomposition:
`(g • f)(x) = f (α_d(g⁻¹) • x)`. The imported generic theorem identifies
this inverse-precomposition stabilizer with the full forward-precomposition
function stabilizer above, deriving joint continuity of the whole discrete
function action for the original subgroup topology.

`normAmbientFunctionStabilizer` maps the local function stabilizer through
the actual inclusion `H_d → G`. An open subset of the open subgroup `H_d`
has open image in `G`, so this image is an `OpenSubgroup G`.
`mem_normAmbientFunctionStabilizer` identifies membership with a proof
`hg : g ∈ H_d` and the entire fixed-function equation for
`normSectionAction ρ hρ d ⟨g,hg⟩`. The subgroup therefore retains both
locus preservation and function fixedness. `normAmbientFunctionStabilizer_le`
proves its containment in the full locus stabilizer.

For a finite index type `ι : Type t`, an arbitrary family of actual charts
`d i`, and functions `f i` on their actual quotient spectra,
`finiteNormFunctionStabilizer ρ hρ d f U` intersects their ambient
function stabilizers with a prescribed `OpenSubgroup G` named `U`.
Its membership lemma gives exactly membership in `U` and, for every `i`,
locus preservation and the full function equation just described.
`finiteNormFunctionStabilizer_le` proves containment in `U`.
No covering, matching-family, distinctness or nonempty-family condition
is needed for this finite simultaneous stabilization result.

## Provenance and limits

This module is internal derived content. It reuses the weighted open
stabilizer construction, the published actual bounded represented-domain
section action, the rational spectrum homeomorphism, the published joint
spectrum-evaluation theorem, and the compact locally constant action theorem.
The proofs above explain how these constructions remove the full
`DomainSpectralAction` hypothesis used by the existing
`DomainContinuousLocus` and `DomainLocallyConstantStabilizer` interfaces
when the domain is a specified actual rational chart.

The original geometric conventions are in Vladimir Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.4, Example 1.2.2(v), Definitions 1.2.3 and 1.2.5,
Exercise 1.2.4 and Fact 1.2.6, supplies the positive-radius algebras,
bounded spectrum, evaluation topology, normalized bound and compactness
context. Printed/PDF p.9, Definition 2.2.1 and Exercise 2.2.2(ii),
supplies the full affinoid-domain and weighted rational-locus conventions.
These pages were read directly. The source's complete-field setting is
retained where full represented section maps are used. The locus-only
continuity argument uses the existing normed-algebra spectrum theorems
without completeness. The chart's explicit unit-generation hypothesis is
retained; no equivalence with the source's no-common-zero condition is claimed.
The continuity and function-stabilizer conclusions here are internally
derived, not attributed as a theorem of those passages.

The field, group, coefficient and finite-index universes are independent.
Trivial valuations, arbitrary positive real radii, arbitrary chosen closed
ideals, nilpotents and zero algebras are allowed. Spectrum and locus
emptiness cause no exception; a finite index type may be empty, in which
case its simultaneous stabilizer is `U`. Coefficients may be empty whenever
the supplied functions exist. No proper-ideal assumption is added.

These results concern point actions and all locally constant functions on
actual rational quotient spectra. They establish neither a general
analytic structure sheaf nor smoothness for arbitrary etale sheaves.
Preservation of arbitrary compact or distinguished domains, comparison
with the full analytic automorphism topology, quasi-etale lifting,
general analytic and equivariant sites, and the Harris tower remain
separate obligations.
