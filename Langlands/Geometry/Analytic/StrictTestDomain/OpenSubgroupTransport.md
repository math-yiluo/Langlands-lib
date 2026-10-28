# Rational transport with actual open operator subgroups

Worker 36 constructed the subgroup and quotient-spectrum interfaces. The
labelled category pattern adapts Worker 13's published `ActionOpens`, as in
`RationalTransport`; both workers are credited in the contribution.

The hypotheses are a complete ultrametric normed field `K`, a presented strict
affinoid algebra `P`, a topological group `G`, and a `RationalSpectralAction G P`.
The universes of `K` and `G` are independent. The action is the published
continuous homomorphism into bounded algebra automorphisms with the restricted
rational spectral topology. The algebra `P` and all rational quotient algebras
are the actual closed-ideal Tate quotients constructed in the imported modules.

## Objects, arrows and subgroup changes

An `OpenSubgroupTransport` object consists of an actual open subgroup `U` of `G`
and a chosen `U`-invariant rational presentation `d`. Invariance means that the
subgroup preserves its locus as a set. It does not require pointwise fixation
or equality of the chosen input presentation under each operator.

A morphism from `(U,d)` to `(V,e)` retains an element `g : G`, a proof that
`gUg⁻¹ ≤ V`, and a proof that the point action of `ρ(g)` maps the source locus
into the target locus. The point action uses the inverse algebra automorphism.
The identity label is one; a morphism labelled `g` followed by one labelled `h`
has label `h * g`. The module proves all category laws by equality of labels.
Distinct labels remain distinct even if `ρ` has a kernel or the locus is empty.

`toRationalTransport` sends the label to the actual bounded automorphism
`ρ(g)` and forgets the subgroup. It need not be faithful. The `inclusion U`
functor inserts the ordinary rational inclusion category for `U` using
identity-labelled arrows. If `V ≤ U`, `subgroupRestriction` gives an arrow
from the same rational quotient with its restricted `V`-action to the object
with its `U`-action. These arrows form `subgroupRestrictionNatTrans` and commute
with every rational inclusion. `translationIso` identifies `(U,d)` with its
actual translate `(gUg⁻¹, ρ(g) • d)`; the inverse has label `g⁻¹`.

For any morphism `f`, `Hom.groupHom` is the actual continuous homomorphism
`k ↦ gkg⁻¹` from its source subgroup to its target subgroup. Continuity follows
from continuous conjugation and the induced subgroup topologies. The identity
and composite homomorphisms are proved to be the identity and composition of
these maps. On subgroup-restriction arrows this homomorphism equals the
published continuous subgroup inclusion.

## Actual quotient algebras and continuous actions

`Hom.restriction` is the bounded algebra pullback constructed by
`RationalTransport` from the rational universal property. Its direction is from
the target quotient algebra to the source quotient algebra, and its structural
identity is

`f.restriction.comp target.baseMap = source.baseMap.comp (ρ(g)).inv`.

Identity and composition agree with the actual bounded identity and composite
maps. On `inclusion U` arrows these maps equal the already constructed ordinary
rational restrictions. On `subgroupRestriction` arrows they are the actual
identity of the unchanged quotient algebra. The latter equality follows from
rational uniqueness and the displayed structural identity at label one.

Each object has the constructed continuous action of its open subgroup on the
actual Banach spectrum of its quotient algebra. Its spectrum map to the ambient
spectrum and every morphism's quotient-spectrum map fit the published labelled
point-action triangle, expressed by `Hom.spectrumMap_restriction`.

`Hom.sectionAction_restriction` proves the precise intertwining formula

`f.restriction.comp sectionAction_target(f.groupHom k).hom =`
`sectionAction_source(k).hom.comp f.restriction`.

Both sides agree after composition with the target structural map: the bounded
restriction and section-action identities reduce this to
`ρ(g)⁻¹ * ρ(gkg⁻¹) = ρ(k) * ρ(g)⁻¹`.
The target rational universal property then proves equality of the actual
bounded maps. Applying this formula to `k⁻¹` and evaluating seminorms proves
`Hom.spectrum_equivariant`. Thus `Hom.equivariantSpectrumMap` is a morphism of
continuous actions from the source spectrum to the target spectrum restricted
along `f.groupHom`. Its underlying continuous function is exactly comap by
`f.restriction`; the module proves the corresponding application formula.

The functors `toAffinoidSpace` and `toTopologicalSpace` realize all objects and
arrows by these constructed affinoid spectra and continuous maps. The
`boundedPresheaf` is contravariant and valued in presented strict affinoid
algebras. Its composite forgetting norms is `algebraPresheaf`, valued in
commutative `K`-algebras. These functors reuse the published realization of
`RationalTransport` rather than postulating quotient maps.

## Provenance and scope

This is derived local infrastructure over a single fixed affinoid algebra.
`InvariantConjugationSite` constructs conjugate open subgroups and translation
of invariant presentations; `InvariantSubgroupRestriction` supplies restriction
of invariance and continuous subgroup inclusions. `RationalTransport` supplies
the unique bounded quotient maps, their functoriality and their spectrum
triangles. `SpectralContinuousAction` supplies the actual continuous subgroup
actions on quotient spectra. The new construction combines these interfaces
with group labels, proves conjugation equivariance, and identifies its ordinary
inclusion and subgroup-change maps.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic spaces*
(1995–1996), the retained `Equish_1996` manuscript, section 1.1, printed/PDF p. 3,
defines a morphism of spaces with operators using a continuous homomorphism
from the source operator group to the target operator group, and gives the
conjugation formula `k ↦ gkg⁻¹`. This motivates the direction and operator map
used here. The registered folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf* has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The source motivates this derived construction; it does not state this
restricted presentation category verbatim.

The module retains the published chosen unit-radius rational presentations and
restricted rational spectral action. It makes no additional nonempty, reduced,
faithful-action, nontrivially-valued or same-universe assumption. It constructs
no Grothendieck topology on the varying-subgroup category. Full analytic
atlases, arbitrary-radius domains, etale and quasi-etale sites, induced analytic
spaces, structure-sheaf descent, cohomology and Harris towers remain separate
obligations of the broader task.
