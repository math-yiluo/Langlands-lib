# Actual induced rational quotient spectra

Worker 36 constructed this specialization of the published balanced topological
induction to the published actual rational quotient spectra. It supplies a
functor of continuous actions of the full operator group and compatible maps
to the actual ambient affinoid spectrum.

## Hypotheses and actual carriers

Fix a complete ultrametric normed field `K`, a presented strict affinoid algebra
`P`, a topological group `G`, and a `RationalSpectralAction G P`. The universes
`u` of `K` and `v` of `G` are independent. An object `X` of
`ρ.OpenSubgroupTransport` retains an actual open subgroup `H` and a chosen
`H`-invariant rational presentation `d`. Its algebra is the actual closed-ideal
Tate quotient from the imported rational-domain construction.

`AmbientSpectrum ρ` is a definitionally equal wrapper of `BanachSpectrum P`.
Its `G`-action is the existing inverse-pullback action through `ρ.toMonoidHom`.
Joint continuity is `ρ.continuous_globalSpectrumAction`.
`X.LocalSpectrum` is a definitionally equal wrapper of
`BanachSpectrum X.domain.obj.algebra`. Its `H`-action is the inverse-pullback
action of the actual forward section automorphism

`ρ.sectionAction d (ρ.invariantStabilizerInclusion H d h)`.

Both actions are constructed by `MulAction.compHom`; their action laws are
inherited from the corresponding automorphism actions. The wrappers retain
which action is specified without adding points, topology, or an analytic
structure. The local topology is the existing spectrum topology. Joint
continuity of the local action is the published rational spectral local
continuity theorem composed with the continuous subgroup inclusion and the
identity of the spectrum. The module gives definitionally equal instances for
both the open subgroup and its underlying `Subgroup`, to accommodate the
interfaces of the categorical rational action and balanced quotient.

## Induced spaces and maps to the ambient spectrum

`X.InducedSpectrum` is the actual balanced quotient

`G ×_H X.LocalSpectrum`,

using `TopologicalInduction.Space` and its quotient topology. Here the
balancing action is `h • (a,x) = (a*h⁻¹,h • x)`, and the full group acts by
`b • [a,x] = [b*a,x]`. The quotient's joint continuity is inherited from the
published construction. `X.inducedMk a x` denotes `[a,x]`, while the continuous
map `X.inducedUnit` sends `x` to `[1,x]`. The module proves its subgroup
equivariance and that it is an open embedding. The latter applies the generic
open-unit theorem to the stored openness of `H`; neither finite index nor
nonemptiness is assumed.

`X.localToAmbient` is comap by the actual bounded structural algebra map
`d.baseMap`. Its subgroup equivariance is exactly the published
`ρ.spectrumMap_smul` theorem, restricted along the actual subgroup inclusion.
The generic continuous equivariant extension constructs `X.ambientMap` with

`X.ambientMap [a,x] = a • X.localToAmbient x`.

The module proves its unit formula and full-group equivariance by the generic
extension identities. Thus this map is constructed from the bounded algebra
map and the actual quotient, rather than included as input data.

## Transport maps and ambient compatibility

For an arrow `f : X ⟶ Y`, write `g = f.label`. The published arrow retains the
actual condition `g*H*g⁻¹ ≤ J`, where `J` is the target subgroup, and its
continuous operator homomorphism is `h ↦ g*h*g⁻¹`.
`Hom.localSpectrumMap f` is comap by the actual bounded quotient pullback
`f.restriction`. The module proves its equivariance for that conjugation
homomorphism using `f.spectrum_equivariant`. Its identity and composition laws
use the published bounded restriction laws and equality of the resulting
seminorms. The ambient formula is the existing labelled spectrum triangle:

`Y.localToAmbient (f.localSpectrumMap x) = g • X.localToAmbient x`.

The continuous seed for induction is

`x ↦ g⁻¹ • Y.inducedUnit (f.localSpectrumMap x)`.

Its source-subgroup equivariance follows from the local spectrum equivariance,
the target unit's subgroup equivariance, and the group identity
`g⁻¹ * (g*h*g⁻¹) = h*g⁻¹`. The generic extension then constructs the actual
continuous map `f.inducedMap`, with formula

`f.inducedMap [a,x] = [a*g⁻¹, f.localSpectrumMap x]`.

The inverse of the label is essential in this convention. Full-group
equivariance follows from the extension theorem. Quotient induction reduces
the identity law to the label-one and local identity laws. It reduces
composition to the local composition law and
`(k*g)⁻¹ = g⁻¹*k⁻¹`, since the composite label of `f` followed by an arrow
labelled `k` is `k*g`.

`Hom.ambientMap_inducedMap` proves the ambient triangle

`Y.ambientMap (f.inducedMap z) = X.ambientMap z`.

On a representative this is the cancellation
`(a*g⁻¹) • (g • X.localToAmbient x) = a • X.localToAmbient x`.
The implemented proof uses quotient induction, the induced-map formula, and
the local ambient formula, followed by the action cancellation law.

## Functor and scope

`inducedSpectrumAction` bundles the full-group quotient action as an
`Action TopCat G`; its laws are the actual scalar-action laws.
`inducedContinuousSpectrum` bundles the proved joint continuity.
`inducedSpectrumFunctor` takes every object and arrow of
`ρ.OpenSubgroupTransport` to these constructed continuous `G`-spaces and maps.
Its categorical identity and composition laws are proved by extensionality
from the pointwise laws above. The output category is
`ContAction TopCat.{max u v} G`, preserving the independent universes of group
and spectrum. `inducedTopologicalSpaceFunctor` forgets these full-group actions.

The construction adds no assumption of a faithful operator action, a nonempty
spectrum, a reduced algebra, or a nontrivial valuation. No faithfulness claim
is made for the induced functor: the source retains raw labels, whereas the
output consists of their actual continuous maps.

This is derived underlying topological infrastructure over one fixed presented
strict affinoid algebra. It establishes no analytic atlas or analytic-morphism
structure on the quotient, no comparison with a chosen coset-copy model, no
retraction or induction-in-stages theorem, and no etale or quasi-etale site or
site equivalence. Structure-sheaf descent and Harris cohomological geometry
remain further obligations.

## Original-source provenance

The motivation is Berkovich's unfinished *Etale equivariant sheaves on p-adic
analytic spaces* (1995–1996), the retained `Equish_1996` manuscript,
Construction 1.1.2, printed/PDF p. 2. That construction uses coset-indexed
copies of an analytic `H`-space for an open subgroup, gives the induced
`G`-action, and extends an equivariant map on each copy by the chosen coset
representative. This module specializes the already published balanced
underlying topological construction to actual rational spectra; the raw-labelled
transport functor and the ambient triangles are derived from its universal
property and the imported rational transport identities. They are not claimed
to be a verbatim statement of the analytic construction in the manuscript.

The registered source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
content SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf* has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The supplied source is an unfinished manuscript, not a published journal
article. The local registered source and public source notes were checked;
no separate source-specific errata file was present.
