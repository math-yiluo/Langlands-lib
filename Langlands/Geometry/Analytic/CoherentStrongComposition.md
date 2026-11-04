# Composition of original compatible strong atlas maps

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
printed p. 18, the composition construction following Proposition 1.2.8
(zero-based PDF index 14), composes strong maps by choosing an admissible chain,
covering its source by inverse images of common final target domains, and
gluing the resulting affinoid morphisms. The registered source is
`berkovich-1993-etale-cohomology`, PDF SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
This module implements this construction on the original compatible
families from `CompatibleStrongMaps`, with their explicit local morphism
compatibility convention. It neither assumes nor claims coherence for
arbitrary old `StrongHom` data having only the weaker nested-chart law.

The actual bounded maps already exist as `saturatedCompPullback`; their
definition itself requires no saturation. For each original source chart,
choose an original intermediate target and then a final target. Compose
the two supplied bounded algebra maps, then use the constructed bounded
`changeMapChart` to reach any requested admissible final chart. That change
uses the actual inverse-image full domains, affinoid quotient algebras and
finite-cover bounded descent. The coefficient algebra stays the original
source chart algebra. The new construction reuses these maps literally.

`chainPullback_isMapChartChange_of_coherent` proves compatibility of any
two admissible chains, using the first original family's coefficient
coherence and preservation of arbitrary chart changes by the second.
`saturatedCompPullback_eq_chainChange_of_coherent` then proves complete
bounded independence from both choices. Source naturality follows by
computing both restrictions through one common admissible chain and
applying coefficient naturality and bounded uniqueness of chart change.
The existing target naturality needs no coherence assumption. Combining
them gives all original two-variable restriction equations.

`StrongHom.coherentComp` assembles the resulting actual strong map, with
continuous map the literal composite and bounded maps exactly those just
described. It assumes only `HasCoherentPullbacks` for each input original
family; it assumes no enlarged morphism, composition output, directedness,
greatest chart or saturation. `coherentComp_pullback` recovers the literal
composite of the supplied bounded maps on every admissible original chain,
not only the chain selected to define it.

The constructed final-target family is itself coherent:
`saturatedCompPullback_change` follows from exact iterated chart change,
and `saturatedCompPullback_isMapChartChange` gives its full coefficient-test
law. These two facts require no input coherence; input coherence is needed
to assemble source naturality. Thus `hasCoherentPullbacks_coherentComp`
proves closure of actual coherent strong maps under composition.

`CompatibleStrongHom.comp` packages this map with the original local-domain
compatibility law, using the proved equivalence with coefficient coherence.
Its underlying continuous map is the literal composite and `comp_pullback`
recovers every admissible original bounded chain. On saturated sources and
intermediates, `coherentComp_eq_saturatedComp` and `comp_eq_saturatedComp`
identify the complete constructed strong map with the existing saturated
composition; the fields agree definitionally, with proof irrelevance for
laws. All presentations use the existing common universe parameters
`u`, `v`, `w`, and retain trivial valuations and arbitrary original charts.

The source motivates the composition by actual inverse-image gluing. The
choice-independence, original-family coherence and comparison results here
are internal consequences of the previously constructed full affinoid
domains and bounded chart change. This is a focused composition unit;
identity and associativity laws, categorical saturation comparison,
localization comparison and the analytic etale sites remain subsequent work.
