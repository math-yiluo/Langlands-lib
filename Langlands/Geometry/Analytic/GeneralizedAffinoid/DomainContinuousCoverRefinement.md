# Actual finite cover refinement diagrams of jointly continuous actions

Author: Worker 56.

This internal construction lifts the existing actual finite-cover refinement
diagram to jointly continuous actions. It retains each cover, chosen
refinement index function, bounded component restriction and total quotient
map.

Let `K : Type u` be a complete ultrametric normed field, let `P` be an
actual finite positive-polyradius presented affinoid quotient over `K`,
and let `G : Type v` be a topological group. The universes are independent.
Fix `ρ : DomainSpectralAction G P`, an open subgroup `H`, and an invariant
represented domain `d : ρ.InvariantDomain H`.

For a supplied finite cover `c` of `d.obj`, assume
`hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)`. This says that `H`
preserves all original component loci. The construction
`invariantCoverSpectrum` restricts the proved jointly continuous
`finiteCoverSpectrum` along the actual continuous inclusion of `H` into
`ρ.finiteFamilyOpenSubgroup H c.obj`. It has the exact preceding
`invariantCoverSpectrumAction` as its underlying action. Its space is
the original topological disjoint union of the component section
spectra. The operator formula preserves the index and applies the
component's inverse bounded section pullback.

`invariantCoverQuotientContinuous` lifts exactly the existing
`invariantCoverQuotient` through the full subcategory of continuous
actions. Its target is the actual represented target locus with its
proved jointly continuous restricted ambient action. Its underlying map
is `TopCat.ofHom c.totalMap`. The surjectivity, closedness and
quotient-map results apply to that unchanged map and topology.

Given two such covers `b` and `c` with preservation witnesses, an
actual refinement `r : Domain.FiniteCover.Refinement b c` gives
`invariantCoverSpectrumMapContinuous`. This lifts the existing
equivariant spectrum map without changing its continuous map or
equivariance equation. Its explicit value is

```text
⟨j, x⟩ ↦ ⟨r.index j, (r.map j).spectrumMap x⟩.
```

Here `r.map j` contains the actual bounded algebra restriction from
the selected coarser component to the finer component. The spectrum map
is pullback along this same bounded map. The theorem
`invariantCoverSpectrumMapContinuous_over_target` retains the original
commuting refinement triangle with both total quotient maps.

`invariantCoverSpectrumContinuousOverFunctor` has source
`ρ.InvariantFiniteCover H d`, the full category of finite covers
preserved componentwise by `H`, with all their chosen actual
refinements. Its target is the overcategory of the jointly continuous
action on `d.obj.locus`. Its objects are the actual continuous
equivariant quotient maps and its arrows are the constructed actual
continuous equivariant refinement maps. After overcategory and
full-subcategory extensionality, its identity and composition laws
are the corresponding laws of the existing equivariant overcategory
functor. The projection formulas expose the exact object actions,
quotient maps and refinement morphisms. Forgetting joint continuity
recovers the full preceding overcategory diagram definitionally.

For an open subgroup `J ≤ H`, the subgroup theorems identify
`ContAction.res` on the spectrum actions, total quotient maps and
individual refinement maps with the same constructions at `J`.
`invariantCoverSpectrumContinuousOverFunctor_subgroup` gives the
corresponding equality of complete overcategory functors. Cover
restriction retains every original cover and chosen refinement.
All these subgroup identities are definitional; preservation witnesses
do not change the ambient group element or the bounded operators.

For arbitrary supplied covers `c` and `b`, the existing
`commonCoverOpenSubgroup H c b` intersects both families' common open
stabilizers inside `H`. Thus `commonCoverSpectrumMapContinuous` realizes
every actual refinement as a continuous equivariant map at that
explicitly constructed subgroup. Its continuous map is again exactly
`TopCat.ofHom r.spectrumMap`. No equality of the two covers' separate
stabilizers is assumed, and the refinement map itself need not be
surjective.

The provenance is internal. This unit combines
`DomainContinuousFiniteCover`, `DomainContinuousLocus` and the concrete
constructions of `DomainEquivariantCoverRefinement` using continuous
subgroup restriction and full-subcategory lifting. The joint continuity
proofs come from the original component spectrum actions; the algebra
maps and all equivariance equations were already constructed.
No new literature theorem is asserted. Supporting common-stabilizer
constructions adapt Worker 36's strict rational finite-intersection
pattern.

Empty covers and loci, zero quotients, nilpotents, empty spectra and
trivial scalar valuations remain allowed. The quotient is onto the target
locus, and no spectrum injectivity or algebra-section descent is claimed.
Analytic atlases, structure sheaves, analytic etale sites, comparison with
all compact analytic-domain tests and the Harris specialization remain
further work.
