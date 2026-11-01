# Birational unramified morphisms are open immersions

`Langlands.AlgebraicGeometry.birationalUnramifiedOpenImmersion` proves exactly
`BirationalUnramifiedOpenImmersionStatement` in arbitrary universe `u`, with no
outer hypotheses. It retains integral source and geometrically unibranch
integral base, separatedness, local finite type, formal unramifiedness, and
Mathlib's actual birationality over the base.

At each source point `z`, write `R` for the base stalk at `f z`, `B` for the
source stalk at `z`, and `K` for the source function field. The birational
generic-stalk comparison makes `K` a fraction ring of `R`, with structure
map the given stalk map followed by specialization to the source generic
point. The stalk map is local, essentially finite type, and formally
unramified. The source stalk embeds in its function field, as an `R`-algebra.
The local algebra corollary
`algebraMap_surjective_of_essFiniteType_unramified_fractionRing_embedding`
therefore makes the actual map `R → B` surjective. It is injective because
its composite into the fraction field `K` is injective. Thus every stalk
map is an isomorphism.

The lemmas in `IntegralLocalSections` spread inverse stalk maps to sections
over base neighborhoods. Each such section is an open immersion by
unramifiedness and a closed immersion by separatedness. Its nonempty
image is dense in the integral inverse-image open and is also closed,
so the morphism over that neighborhood is an isomorphism. These local
isomorphisms give injectivity and the source-local open-immersion criterion.

This is the scheme globalization of the algebraic proof supporting EGA IV,
fourth part, Remark 18.10.2(iii), printed pp.158–159, and Lemma 18.10.18,
printed pp.166–167. Its registered original source is
`grothendieck-dieudonne-ega-iv4-1967`, SHA256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
The implemented proof uses the normalization and algebraic Zariski Main
route established in the local algebra proof, followed by stalk comparison
and spreading; it adds no noetherianity, normality or finite presentation
assumptions. Worker 336 authored the local algebra proof and Worker 208
authored the generic-stalk and scheme globalization arguments.
