# Locally constant presheaves for represented-domain spectral rational actions

Author: Worker 56. Internal construction.

## Inputs and the original compact point diagrams

Fix a complete ultrametric normed field `K`, an actual
`PresentedAffinoidAlgebra K`, an arbitrary topological group `G`, and a
`DomainSpectralAction G A`. This input is a bounded algebra automorphism
action continuous for the already constructed represented-domain spectral
topology. It does not assume continuity of base-algebra orbits in the
quotient norm. All declarations in this file retain `CompleteSpace K`.
The field, group and coefficient set have independent universes `u`, `v`
and `w`.

For an open subgroup `H`, the existing `SpectralInvariantChart ρ H` is the
full category of original positive-radius rational quotient presentations
whose actual loci are preserved by `H`. Its arrows are all original bounded
restrictions over the fixed base algebra. The subgroup has its original
subspace topology. No condition is added to these arrows.

`spectralInvariantCompactLocusFunctor` lifts the existing continuous locus
action diagram to the full category `CompactContinuousAction H`. The
compactness proof uses the actual closed rational inequalities in the
compact ambient Banach spectrum. The loci retain their original subspace
topologies. `spectralInvariantCompactSpectrumFunctor` similarly lifts the
existing diagram of original rational quotient spectra and bounded spectrum
pullbacks, using their existing compactness instances and actual spectrum
topologies. These lifts leave all point maps and action operators unchanged.

## Entire locally constant function spaces

`spectralInvariantLocusLocallyConstantPresheaf` and
`spectralInvariantSpectrumLocallyConstantPresheaf` compose the opposites of
these diagrams with the existing
`CompactContinuousAction.locallyConstantFunctor H C`. They take values in
`ContAction TopCat.{max u w} H`. Each value is the entire set of locally
constant functions from the original locus or quotient spectrum to an
arbitrary set `C`, wrapped in `DiscreteLocallyConstant` and equipped with
its own discrete topology. No topology, action, nonemptiness or chosen
default element is required on `C`.

The action is inverse precomposition: `(g • f)(x) = f(g⁻¹ • x)`. Its joint
continuity is proved by the imported compact-action construction: compactness
and continuity on the point space give open stabilizers for every locally
constant function, hence a continuous action on this entire discrete
function space. Joint continuity is a consequence, not a new input.
The two `...Presheaf_action_apply` lemmas give the original point operators
explicitly. On a quotient spectrum the point operator at `g⁻¹` is
`BanachSpectrum.comap` of the bounded inverse of
`(spectralInvariantSectionAction ρ H d).actionAut g⁻¹`.

Every original chart restriction `q : d ⟶ e` induces pullback from the
functions on `e` to the functions on `d`. The two `...Presheaf_map_apply`
lemmas identify its pointwise value with `f (q.hom.locusMap x)` and
`f (q.hom.spectrumMap x)`, respectively. The imported compact functor proves
equivariance using the equivariance of the original point maps; continuity
of function pullback follows from the discrete domain topology. Its
functoriality retains all original bounded restrictions.

## Original comparison and subgroup coherence

`spectralInvariantCompactSpectrumLocusIso` lifts the existing natural
continuous equivariant spectrum-locus homeomorphism into the full compact
action category. Naturality is the original naturality, and both component
maps are unchanged. Applying the contravariant locally constant functor
gives `spectralInvariantLocallyConstantPresheafIso`, an isomorphism from
the locus function presheaf to the quotient-spectrum function presheaf.
Its forward component sends `f` to `f ∘ d.obj.locusHomeomorph`; its inverse
sends `f` to `f ∘ d.obj.locusHomeomorph.symm`. The two application lemmas
prove these formulas by reduction. All locally constant functions are used:
no additional condition on fibers is required because the original rational
spectrum map is a homeomorphism onto its locus.

For open subgroups `H ≤ J`, the existing full chart inclusion goes from
`J`-invariant charts to `H`-invariant charts, while continuous group
restriction goes from `J`-actions to `H`-actions. The theorems
`spectralInvariantLocusLocallyConstantPresheaf_subgroup` and
`spectralInvariantSpectrumLocallyConstantPresheaf_subgroup` identify
precomposition of the `H` presheaf by that chart inclusion with
postcomposition of the `J` presheaf by `ContAction.res` along the original
continuous subgroup inclusion. These are literal equalities of functors:
the full function sets, discrete topologies, operators and restrictions
are unchanged. `spectralInvariantLocallyConstantPresheafIso_subgroup`
gives the corresponding equality of the two natural comparison
isomorphisms, including their original inverse maps.

## Provenance and scope

This internally adapts Worker 56's published
`RationalNormLocallyConstantPresheaf` and the presheaf subgroup identities
from `RationalNormLocallyConstantSheaf` to the published
`RationalSpectralInvariantActions` and `RationalSpectralInvariantRestriction`
diagrams. Those spectral diagrams retain their attribution to Workers 56
and 36. The compact-action function construction is reused unchanged.
The norm-continuity hypothesis is replaced by the actual
`DomainSpectralAction` input, and completeness is retained throughout;
no comparison of norm and spectral actions is asserted.

The inherited domain conventions are Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), printed/PDF p.9 Definition 2.2.1 and
Exercise 2.2.2(ii)-(iii), p.10 Fact 2.2.3(i) and Definition 2.2.7:
represented affinoid domains, positive-radius rational quotient
presentations, intersections, spectrum-locus identification and domain
embeddings. Registered source `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The original presentations use explicit unit generation as a sufficient
condition for absence of common zeros; no converse is claimed.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript, section 1.1 printed/PDF pp.1-3, supplies the motivation
for continuous operators, continuous acting-group homomorphisms and
equivariant maps. Registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf*, SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The manuscript's automorphism topology tests compact analytic domains;
this contribution uses the already constructed represented-domain spectral
topology without identifying it with that full analytic topology. Neither
source is claimed to state this internal function-presheaf construction.

Arbitrary positive real radii, trivial valuations, nilpotents, zero quotient
algebras, empty spectra and loci, and empty coefficient sets are retained.
Sheaf descent, analytic algebra sheafness, general analytic atlases, full
analytic automorphism topology comparison, compact/distinguished-domain
lifting, analytic etale/quasi-etale sites and the Harris tower remain
separate obligations. This is a local prerequisite, not host-task completion.
