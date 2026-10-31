# Refinement naturality of continuous families under rational localization

Author: Worker 56.

This module proves that extension and restriction of continuous families
inside an actual rational chart commute with chosen-index finite full-domain
refinements. It constructs both natural isomorphisms of compatible-family
presheaves and identifies their components with actual restriction and
quotient-topology gluing.

## Inputs and constructions reused

The coefficient field is a complete ultrametric normed field. Affinoid
algebras are the Library's actual quotients of finite positive-polyradius
Tate algebras by closed ideals, with their quotient norms and chosen
presentations. Full domains retain their actual algebra, bounded structural
map, closed locus, exact spectrum image and universal factorization against
every presented affinoid test. Rational charts retain explicit unit
generation and arbitrary positive radii.

`RationalChartCoverGluing` constructs extension and restriction of local
continuous maps through actual component locus homeomorphisms, their inverses
and the equivalences on compatible-family subtypes. It proves global
restriction, gluing and spectrum assembly equations.
`RationalChartCoverRefinement` constructs the actual extension and
restriction functors on finite covers and their refinements. Every chosen
index, component algebra and bounded restriction is retained.

The target `Y : Type v` is an arbitrary topological space, with universe
independent of the coefficient universe `u`. No Hausdorff hypothesis is
used. `DomainCoverDescent` supplies refinement pullback and its constructed
inverse: glue the finer compatible family, then restrict the resulting
global continuous map to the coarser cover.
`DomainCoverFamilyNaturality` supplies the actual presheaf
`compatibleFamilyPresheaf` with values in `Type (max u v)`, the concrete
`gluingNatIso`, and the spectrum assembly equation for refinement pullback.

## Refinement squares

For an inner refinement `r : Refinement b c`,
`extendCoverFamily_pullbackFamily` identifies extension of a pulled-back
family with pullback of the extended family along the actual extended
refinement. It holds for every family, before overlap agreement is imposed.
The proof applies extensionality and the proved naturality of inverse
component locus homeomorphisms.

For an ambient target `V`, an actual inclusion `f` into the rational chart,
and a refinement of covers of `V`, `restrictCoverRefinement_locusMap`
proves the corresponding component diagram. The two maps have equal
underlying spectrum points. The theorem
`restrictCoverFamily_pullbackFamily` follows by precomposing the selected
coarser component map with this equality. It also holds for every family
and retains the supplied chosen index function.

`extendCoverFamilyEquiv_pullback` and
`restrictCoverFamilyEquiv_pullback` lift these squares to compatible
families by subtype extensionality. The two
`pullbackEquiv_trans_*CoverFamilyEquiv` theorems give equality of the
composite equivalences themselves. The two
`*CoverFamilyEquiv_pullbackEquiv_symm` theorems give the inverse descent
squares: transport of a finer family's descent equals descent after
transport. Each proof applies injectivity of the transported refinement
equivalence, uses the forward square, and cancels the constructed
equivalences against their inverses.

The two `*CoverFamily_spectrumFamilyMap_pullbackFamily` theorems
identify assembly after transported refinement pullback with the original
coarser assembly precomposed by `r.spectrumMap`. Their proofs combine
the raw-family square, unchanged assembly under rational localization,
and the existing refinement assembly equation. They compare continuous
maps on the same finite disjoint unions of actual component quotient
spectra and do not require family compatibility.

## Natural isomorphisms and gluing

`extendCoverFamilyNatIso d U Y` has source
`compatibleFamilyPresheaf U Y` and target the compatible-family presheaf
of `d.extendDomain U`, precomposed with
`(d.extendFiniteCoverFunctor U).op`.
`restrictCoverFamilyNatIso d f Y` has source the presheaf for the ambient
target `V` and target the presheaf for `d.restrictDomain V f`, precomposed
with `(d.restrictFiniteCoverFunctor f).op`.

Each component is the already constructed actual family equivalence,
converted to an isomorphism in the category of types. The compatible
refinement square proves naturality; `NatIso.ofComponents` constructs
the inverse natural transformation. The `hom_app` and `inv_app` lemmas
expose both component maps as these actual equivalences and inverses.
The two `*CoverFamilyNatIso_gluing` equations state that the forward
component applied to the restrictions of a global continuous map agrees
with the restrictions after composition with the target locus comparison.
Extension uses the inverse target homeomorphism; restriction uses the
forward one. These equations follow from the actual family/gluing
equations in `RationalChartCoverGluing`. The inverse gluing components
remain the concrete quotient lifts supplied by `gluingNatIso`.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p.9, supply the
full affinoid-domain and positive-radius rational-quotient context.
Fact 2.2.3(i) and Definition 2.2.7, printed/PDF p.10, supply the
represented-spectrum and domain-embedding context. Explicit unit generation
remains in force, without an asserted equivalence to absence of common
zeros.

The refinement squares and natural isomorphisms are internally derived
from actual domain localization and continuous quotient-gluing
constructions. They are not separately numbered assertions from these
pages. The existing bounded-base-equivalence construction in
`DomainCoverFamilyNaturality` supplies the categorical pattern; the present
rational structural map need not be an algebra equivalence.

Empty finite covers, empty loci, zero algebras, nilpotents and trivial
valuations remain permitted at the existing chosen-presentation scope.
This module does not assert algebra or module descent, Tate acyclicity,
rational-type flattening, general analytic pullbacks, analytic atlases
or etale/equivariant sites.
