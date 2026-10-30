# Continuous descent under finite full-domain refinements

Worker 56 constructs actual restriction of compatible continuous families
along a supplied refinement of finite full-domain covers. The restriction is
an equivalence, and it preserves the continuous map obtained by gluing.
The declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover`.

## Inputs and provenance

The field `K : Type u` is complete and ultrametric. The ambient algebra is a
presented finite positive-polyradius Tate algebra modulo a closed ideal, with
its quotient norm. Every component is a full domain in this same ambient
algebra's actual bounded multiplicative-seminorm spectrum. Each representation
retains its quotient algebra, bounded structural map, closed locus, exact
spectrum image and universal factorization against all presented affinoid
tests. A domain arrow retains its actual bounded algebra restriction.

The imported `DomainCoverRefinement` supplies finite covers and their
refinements: `r : Refinement d c` selects `r.index j` in the coarser cover
for each finer component, and an actual domain arrow
`r.map j : d.obj j ⟶ c.obj (r.index j)`. The imported `DomainGluing` proves
that continuous maps on the target locus are equivalent to compatible
continuous maps on the component loci. Its gluing construction uses the
quotient map from the finite disjoint union of actual representing spectra;
neither injectivity of a representing-spectrum map nor algebra-section
gluing is an input.

The original domain notion is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), registered source
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
Definition 2.2.1 on printed/PDF p.9. Definition 2.2.7 on p.10 supplies the
affinoid domain embedding context. The restriction and descent equivalence
here are internal consequences of the published full-domain arrows,
cover refinements and continuous gluing, rather than separately named
theorems in that source.

## Restriction and gluing

`CompatibleFamily c Y` abbreviates the subtype of families of continuous
maps from `c`'s component loci to `Y` that agree at equal underlying ambient
spectrum points. The topological target has its own universe `v`, independent
of `u`; no separation or compactness condition is imposed on it.

`Refinement.pullbackFamily r g` has component
`(g (r.index j)).comp (r.map j).locusMap`. Thus restriction uses the
continuous locus inclusion induced by the stored bounded restriction.
It does not select unrelated component maps. Equality of ambient points is
preserved by these inclusions, so compatibility of `g` proves compatibility
of its restriction. `pullback` bundles this family and its proved
compatibility; `pullback_apply` exposes the formula.

`pullback_id` and `pullback_comp` prove that identity and successive
refinement restriction act as expected. The proofs use subtype, function
and continuous-map extensionality; the locus inclusions preserve the
underlying ambient point. `pullbackFamily_restrict` proves that restricting
a global continuous map to the coarser cover and then through a refinement
gives its restriction to the finer cover. `pullback_gluingEquiv` expresses
this as commutation with the published gluing equivalences.

`glue_pullbackFamily` proves that refining a compatible family leaves its
glued continuous map unchanged. The proof applies uniqueness of gluing on
the finer cover. Each restriction of the coarser glued map is the original
coarser component map, and composing with the actual refinement inclusion
gives the required finer component.

## Equivalence and independence of choices

The entry construction `Refinement.pullbackEquiv` has forward map
`pullback`. Its inverse glues a finer compatible family and restricts the
result to the coarser cover. The left inverse follows from gluing
invariance and the coarser restriction-of-gluing equation. The right
inverse follows from restriction of a global map through the refinement
and the finer restriction-of-gluing equation. This constructs an inverse
without assuming that every coarser index is selected or that every
individual refinement inclusion is surjective.

`pullback_eq` proves that any two refinements between the same covers
act identically on compatible families. After applying the inverse of
the finer gluing equivalence, both yield the glued coarser map. This does
not identify the actual refinement arrows or their chosen index functions.
`pullbackFamily_postcomp` proves compatibility with each continuous map
of topological target spaces, whose universe is independently `w`.

All constructions allow zero cover size, empty loci, zero quotient
algebras and trivial valuation. They concern continuous maps on represented
loci and supplied refinements in one ambient spectrum. Actual algebra
sections, analytic structure sheaves, intersections, pullback stability
along arbitrary analytic maps, analytic atlases and etale sites remain
separate obligations.
