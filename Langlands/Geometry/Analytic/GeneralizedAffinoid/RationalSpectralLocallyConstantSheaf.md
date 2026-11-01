# Continuous-action-valued locally constant sheaves on spectral-invariant rational sites

Author: Worker 56. Internal construction.

## Geometric inputs and original functions

Fix a complete ultrametric normed field `K`, an actual
`PresentedAffinoidAlgebra K`, an arbitrary topological group `G`, and a
`DomainSpectralAction G A`. This is an action by actual bounded algebra
automorphisms, continuous for the constructed represented-domain spectral
topology. No continuity of algebra orbits in the quotient norm is assumed.
Every declaration in this file retains `CompleteSpace K`. The field, group
and coefficient set have independent universes `u`, `v` and `w`.

For an open subgroup `H`, use the existing full category
`SpectralInvariantChart ρ H` and its finite rational Grothendieck topology.
Its objects are the original positive-radius rational quotient presentations
whose actual loci are preserved by `H`; its arrows are all original bounded
restrictions over the fixed base algebra. The acting subgroup retains its
original subspace topology.

The imported `spectralInvariantLocusLocallyConstantPresheaf` consists of every
locally constant function from each original locus subspace to an arbitrary
coefficient set `C`. Its `DiscreteLocallyConstant` wrapper equips this entire
function set with the discrete topology. The action is inverse precomposition
by the existing jointly continuous locus action. The imported compact-action
construction proves that this discrete function action is jointly continuous;
continuity is a consequence of compactness and the actual point action.
The spectrum presheaf similarly uses every original quotient spectrum, its
actual topology and action, and the original bounded restriction maps.
There is no topology, action, nonemptiness hypothesis or chosen default
element on `C`.

`spectralInvariantLocusLocallyConstantForgetIso` removes the discrete wrapper
and forgets the action, identifying the underlying set-valued presheaf with
the ordinary locus presheaf precomposed with the original invariant-chart
inclusion. Its component maps are `toLocallyConstant` and
`DiscreteLocallyConstant.mk`.
`spectralInvariantSpectrumLocallyConstantForgetIso` does the same on the
original quotient spectra.
`spectralInvariantLocallyConstantPresheafIso_forget` identifies the forgotten
natural comparison with the original ordinary spectrum-locus comparison.
Both directions retain pullback by the original rational homeomorphism and
its inverse. These identifications follow from the definitions.

## Categorical sheaf construction

First, `spectralInvariantLocusLocallyConstantForget_isSheaf` uses the proved
continuity of the actual invariant-chart inclusion and the already constructed
ordinary locally constant sheaf. Transport through the forgetful isomorphism
above proves that the full underlying function presheaf is a sheaf.

The helper `spectralInvariantDiscretePresheaf_isSheaf` applies to any presheaf
`F` of continuous `H`-actions on topological spaces on this finite invariant
site, provided every `F(d)` has discrete topology and its underlying
set-valued presheaf is a sheaf. It proves Mathlib's full categorical sheaf
condition: for every test continuous action `E`, the presheaf of continuous
equivariant maps from `E` into `F` has unique amalgamation. The test space
`E` is arbitrary and is not assumed discrete or compact.

For a covering sieve `S` and a compatible family of maps from `E` to its
section spaces, evaluate at each point `x` of `E`. The underlying set-valued
sheaf uniquely glues this compatible family to a section `q(x)`. Its recovery
equation holds for every member of the entire sieve. Extract a finite
covering family `f_i : D_i ⟶ d` inside `S` and form the restriction map

`r : F(d) → ∏ i, F(D_i)`.

The generated sieve of this finite family is covering. Its separatedness,
transferred to the generating presieve by
`Presieve.isSeparatedFor_iff_generate`, proves that `r` is injective.
Because the family is finite, the product of its discrete section spaces is
discrete. Thus `r` is a closed embedding: it is continuous from a discrete
domain, injective, and closed because every subset of the discrete codomain
is closed. The recovery equations identify `r ∘ q` with the tuple of supplied
continuous local maps. Continuity of that tuple and the embedding criterion
prove continuity of `q` in the original topology of `E`.

For equivariance, restrict both sides of the desired equation along every
`f_i`. Equivariance of the presheaf restrictions and the supplied local maps,
together with recovery, gives equality in every component. Injectivity of
`r` gives equality in `F(d)`. The same injectivity proves uniqueness of the
glued continuous equivariant map. This proves the categorical sheaf condition
directly, including continuity of the amalgamation.

Applying the helper to the actual discrete locus function spaces gives
`spectralInvariantLocusLocallyConstantPresheaf_isSheaf`. Transport through
the existing natural continuous equivariant spectrum-locus isomorphism gives
`spectralInvariantSpectrumLocallyConstantPresheaf_isSheaf`.
The definitions `spectralInvariantLocusLocallyConstantSheaf` and
`spectralInvariantSpectrumLocallyConstantSheaf` package exactly these
presheaves as Mathlib sheaves with coefficients in
`ContAction TopCat.{max u w} H`.
`spectralInvariantLocallyConstantSheafIso` lifts their original natural
comparison without changing either component map.

Empty finite covering families are allowed. The restriction map then has
empty product as codomain, and separatedness still proves its injectivity.
The argument requires no inhabited index type, nonempty locus, nonempty
coefficient set or nonzero quotient algebra.

## Subgroup and comparison coherence

For open subgroups `H ≤ J`, the full chart inclusion goes from `J`-invariant
to `H`-invariant charts. Its continuous-site sheaf functor therefore
precomposes sheaves from the `H`-invariant site to the `J`-invariant site.
Continuous acting-group restriction goes from `J`-actions to `H`-actions
along `openSubgroupInclusion h`.

The imported theorems
`spectralInvariantLocusLocallyConstantPresheaf_subgroup` and
`spectralInvariantSpectrumLocallyConstantPresheaf_subgroup` identify
precomposition of the `H` function presheaf by chart inclusion with
postcomposition of the `J` function presheaf by action restriction.
The imported `spectralInvariantLocallyConstantPresheafIso_subgroup` gives
the same equality for the comparison isomorphisms. These three presheaf
identities are defined in `RationalSpectralLocallyConstantPresheaf`.
They retain all original functions, topologies, point operators, bounded
restrictions and homeomorphisms.

The two `spectralInvariant...LocallyConstantRestrictedSheaf` definitions
package the original `J` presheaves with action restricted to `H`.
Their sheafness follows from the actual chart-inclusion sheaf functor and
the imported presheaf identities.
`spectralInvariantLocusLocallyConstantSheaf_subgroup` and
`spectralInvariantSpectrumLocallyConstantSheaf_subgroup` give the resulting
equalities of sheaf objects.
`spectralInvariantLocallyConstantRestrictedSheafIso` retains the original
comparison with its action restricted to `H`.
`spectralInvariantLocallyConstantSheafIso_subgroup` identifies it with the
image of the `H` sheaf comparison under the chart-site sheaf functor.
All three sheaf equalities follow from the definitions; proof irrelevance
accounts for the sheaf-property fields.

## Provenance and scope

This internally adapts Worker 56's published
`RationalNormLocallyConstantSheaf` to represented-domain spectral actions.
The geometric inputs, ordinary locally constant sheaf and compact-action
function presheaves are reused. The finite-cover continuous gluing proof is
adapted in this file. Mathlib supplies the categorical sheaf definition,
underlying-set amalgamation, separatedness and embedding tools; the
continuous-action-valued sheaf property is proved here. The norm-orbit
continuity hypothesis is replaced by `DomainSpectralAction`, with
completeness retained throughout. No comparison of norm and spectral
actions is used. The imported spectral invariant-site and restriction-site
constructions retain their attribution to Workers 56 and 36.

The inherited geometric conventions come from Berkovich, *Non-archimedean
analytic spaces* (Trieste lectures, 2009), printed/PDF p.9 Definition 2.2.1
and Exercise 2.2.2(ii)-(iii), and p.10 Fact 2.2.3(i) and Definition 2.2.7:
represented affinoid domains, positive-radius rational quotient
presentations, intersections, spectrum-locus identification and domain
embeddings. Registered source `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The original presentations retain explicit unit generation as a sufficient
condition for absence of common zeros; no converse is asserted.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript, section 1.1 printed/PDF pp.1-3 and section 1.2 p.3,
motivates continuous operators, continuous acting-group homomorphisms,
equivariant maps, geometric covering families and site/sheaf functoriality.
The registered folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf*, SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Its automorphism topology tests compact analytic domains; the present input
uses the constructed represented-domain spectral topology without
identifying it with that full topology. Neither original is claimed to state
this internal finite-site categorical gluing result or identify these
coefficient-action sheaves with the full equivariant etale or quasi-etale
sheaf categories.

Arbitrary positive real radii, trivial valuations, nilpotents, zero
quotients, empty spectra and loci, and empty coefficient sets are retained.
General analytic algebra sheafness, analytic atlases, full analytic
automorphism topology comparison, compact/distinguished-domain lifting,
analytic etale/quasi-etale sites and the Harris tower remain separate
obligations. This local construction does not complete the host task.
