# Composition and refinement of finite full-domain covers

Worker 56 constructs refinements and composition for supplied finite covers
of a full affinoid domain. The declarations belong to
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover`.

## Inputs and provenance

The field `K : Type u` is a complete ultrametric normed field, with possibly
trivial valuation. The base `A : PresentedAffinoidAlgebra K` and every domain's
representing algebra are the published finite positive-polyradius closed Tate
quotients with their actual quotient norms. A `Domain K A` stores a bounded
structural map, a closed locus in `BanachSpectrum A`, its exact structural
image, and the universal factorization property against all presented
positive-polyradius affinoid tests. A domain arrow stores the actual bounded
algebra restriction in the opposite direction, with its equation over `A`.
The imported `Domain` module proves uniqueness of these arrows.

The registered original is V. G. Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), source ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 on printed/PDF p.9 supplies the closed-locus, exact-image
and full affinoid-test clauses of the imported domain construction.
Definition 2.2.7 on p.10 gives the source context of affinoid domain
embeddings. The new finite-family operations are internal consequences of
the imported domain arrows and pointwise covering; the source does not
separately state these chosen finite-ordinal constructions.

The imported `DomainTopology` defines `FiniteCover V` using a natural number,
a family of `Domain K A` indexed by its finite ordinal, actual restriction
arrows into `V`, and pointwise coverage of `V.locus`. Its `totalMap` is the
continuous map from the disjoint union of the actual component spectra to
that locus. Only these published domain and cover constructions are used.

## Finite families and refinements

`ofFintype` converts a family indexed by any `Fintype ι`, with `ι : Type v`,
to this finite-ordinal cover representation. Its size is `Fintype.card ι`.
It transports the objects and actual arrows along
`(Fintype.equivFin ι).symm`, and transports each covering witness along the
forward equivalence. The index universe is independent of the field universe.

A `Refinement d c` selects `index j : Fin c.size` for every finer component
`j : Fin d.size`, together with an arrow
`map j : d.obj j ⟶ c.obj (index j)`. This retains the actual bounded map
from the chosen coarser algebra to the finer algebra. The equation
`over_target` shows that this arrow followed by the coarser target arrow
equals the finer target arrow. It follows from the imported uniqueness of
full-domain arrows, rather than being an extra assumption on refinements.

`Refinement.ext` proves equality of refinements with equal index functions,
using that same arrow uniqueness. `Refinement.id` uses the component
identities, and `Refinement.comp` composes index functions and actual
arrows. The category instance on `FiniteCover V` proves its laws by
`Refinement.ext`. Refinement arrows can have different index functions,
including when a cover repeats a domain, so this category is not asserted
to be thin.

`Refinement.toSingleton` selects the sole component of the identity cover
and uses the supplied cover's target arrows. `singletonIsTerminal`
constructs its categorical terminality: every index function into `Fin 1`
is equal, after which arrow uniqueness identifies the refinements.
This includes a cover with zero components.

## Actual spectrum maps

For a refinement `r : Refinement d c`, `Refinement.spectrumMap` is a
continuous map

`(Σ j : Fin d.size, BanachSpectrum (d.obj j).algebra) →
 (Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra)`.

It sends `⟨j,x⟩` to the chosen coarser index and the pullback of the bounded
multiplicative seminorm `x` along the stored bounded algebra restriction.
Continuity follows componentwise from the published continuous spectrum
map of that restriction and continuity of insertion into the topological
disjoint union. `spectrumMap_over_target` proves the equality of continuous
maps `c.totalMap.comp r.spectrumMap = d.totalMap`. Its pointwise proof uses
the published equation `Inclusion.spectrumMap_over_base`, then subtype
extensionality in the fixed target locus.

## Composition of supplied covers

Given `c : FiniteCover V` and `d i : FiniteCover (c.obj i)`, `bind c d`
uses the finite dependent index type `Σ i : Fin c.size, Fin (d i).size`.
Its component at `⟨i,j⟩` is `(d i).obj j`, and its target arrow is
`(d i).map j ≫ c.map i`. Given a point of `V.locus`, first the coverage
of `c` supplies `i`, and then the coverage of `d i` supplies `j`.
`ofFintype` reindexes this family to a finite ordinal.

`bind_size` proves that the new size is `∑ i, (d i).size`, using the
cardinality of a finite dependent sum. `bindIndex` names the index of any
chosen pair, and `bind_obj_bindIndex` identifies its domain by the inverse
law of `Fintype.equivFin`. The entry construction `bindRefinement` sends
each new component to its outer component using the actual inner
restriction. `bindRefinement_index` proves that `bindIndex d i j` maps to
`i`. Coverage and all these constructions allow zero component counts.

Every inner component in this construction is already a `Domain K A`,
in the same fixed ambient spectrum as the outer components. A domain
given only relative to a component's representing algebra is different
input data; promoting it to an ambient full domain is a separate
representation obligation. This unit constructs no intersection
representations, pullbacks of covers along arbitrary maps, algebra-section
gluing, analytic structure sheaf, analytic atlas or etale site. In
particular, cover composition here does not prove the base-change axiom
needed for a pretopology, and no injectivity of representing-spectrum
maps is used.
