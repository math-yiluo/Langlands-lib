# Chosen atlas isomorphisms from bounded chart equivalences

Author: Worker 36.

For supplied `AffinoidAtlasPresentation` objects `A` and `B` over a complete
ultrametric normed field `K`, `ChartEquivData A B` contains an equivalence `e`
of chart indices, preservation and reflection of actual chart-range containment,
and actual bounded algebra equivalences
`B.atlas.algebra (e i) → A.atlas.algebra i`. Both directions of each algebra
equivalence are bounded. The forward bounded maps commute with the supplied
atlas restrictions as equality of bounded algebra maps. No ambient function,
inverse function, continuity proof or ambient chart formula is input. The field,
space and index universes `u`, `v` and `w` remain independent.

`chartOrderIso` is the resulting order isomorphism on the actual chart-containment
partial orders. `forwardData` forgets the inverse algebra maps and retains the
forward monotone choices and restriction squares. `inversePullback` uses the
bounded inverse at `e.symm j`, with explicit transport of its target algebra along
`e (e.symm j) = j`. The heterogeneous equalities `inversePullback_heq` and
`inversePullback_index` identify this transported map with the original bounded
inverse at corresponding indices. `inverse_mono` follows from the inverse order
isomorphism.

`inverse_restriction_comm` proves the inverse bounded restriction square. After
writing both target indices as images under `e`, the proof treats the inverse
indices as free indices equal to the original ones, substitutes these equalities,
and uses the retained heterogeneous map equalities. It then applies injectivity
of the original algebra equivalence to the proposed equality on an algebra
element. Evaluating the forward restriction square at the bounded inverse of
that element and cancelling the algebra inverse pairs proves the equation.
Thus `inverseData` constructs compatible bounded data in the reverse direction.

`hom` and `inv` apply the published `ChartMapData.toHom` reconstruction to these
two systems. In particular their ambient continuous maps are constructed by the
actual spectrum-chart colimit. They retain the specified chart choices and
bounded maps. `hom_inv_id` and `inv_hom_id` prove equality of the full chosen atlas
arrows. The equivalence `ChartMapData.homEquiv` reduces these equations to equality
of bounded chart data. Index equality is the corresponding inverse law of `e`.
Heterogeneous function extensionality reduces the dependent bounded-map families
to each chart, where index substitution and bounded algebra inverse laws identify
the composites with bounded identity maps. Reconstruction then also recovers the
ambient identity maps. The argument never identifies algebra maps merely from
equality on spectrum points.

`iso` bundles these arrows and both proved composition laws into an isomorphism
in the published category of chosen atlas presentations. `homeomorph` uses their
actual ambient maps and continuity proofs, with inverse laws obtained by
projecting the arrow equations to points. `homeomorph_chart` identifies its chart
formula with the spectrum homeomorphism of the original bounded algebra
equivalence. `homeomorph_symm_chart` gives the inverse formula for every target
index using the transported bounded inverse; `homeomorph_symm_chart_index` uses
the original inverse spectrum homeomorphism at corresponding indices.
`homeomorph_image_chart` proves that each whole source chart maps onto its partner
chart: the forward formula gives containment, and surjectivity of the local
spectrum homeomorphism gives the reverse containment.

This is derived infrastructure for the chosen-presentation specialization.
Berkovich, *Etale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.2.3 and Remark 1.2.4(i)-(ii), printed p.16/PDF p.13, give the actual
atlas algebras, spectrum charts, bounded restriction composition and the category
of atlases on a fixed net. Definition 1.2.7, printed p.18/PDF p.15, motivates
compatible morphisms of affinoid charts over a continuous ambient map. Here the
additional equivalence of chart-containment orders and compatible bounded
algebra equivalences provide the inputs from which both ambient maps are
constructed. The isomorphism and homeomorphism are consequences of the published
chosen-map reconstruction and algebra inverse laws; they are not attributed
verbatim to Berkovich. The registered source is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Original PDF pp.13-15 were reread for this construction; the source-specific
errata-note search found no matching note.

The supplied actual atlases remain input. This construction handles a compatible
bijection of their chosen charts. It does not identify all analytic isomorphisms
with such data or construct arbitrary changes of atlas, Berkovich's extended
atlas of Proposition 1.2.6, localization by refinements, general strong-morphism
composition, section-algebra gluing, structure sheaves or analytic sites.
