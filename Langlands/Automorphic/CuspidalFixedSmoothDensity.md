# Fixed-level derivative density in actual cuspidal Hilbert completions

Let `T` be an actual cuspidal operator realization over a number field with
compact additive adelic quotient. Fix its supplied invariant positive form
and a full adelic bounded action on the form's Hilbert completion that agrees
with the completed finite and compact actions. The fixed smooth space uses
the infinite action in the published mixed coordinates.

The existing block diagonal complexification restricts to a faithful
representation of the standard compact subgroup. Continuity of its orbits
follows entrywise. The infinite action preserves the completed fixed
subspace at every open finite level since the adelic factors commute. On
this closed subspace, compact averaging gives dense compact-finite smooth
vectors for the topology of all genuine word derivatives.

The continuous linear equivalence between the restricted and ambient
fixed smooth spaces transports density to the ambient derivative subspace
topology. The closed Hilbert subspace inclusion intertwines the compact
action, so the images of the approximants still have finite-dimensional
compact orbit spans. Fixedness under the open subgroup supplies finite
smoothness. The published joint admissibility of `T` supplies joint vector
recovery, which recovers each compact-finite fixed vector from the original
carrier. Equivariance and injectivity of the canonical embedding show that
the recovered original vector is fixed at the same level. The dense set of
compact-finite approximants thus lies in the original fixed smooth image.
This is an internal consequence of compact smooth density, the invariant
subspace comparison and joint vector recovery.

`FixedLevelDensityStatement` records the density at every open finite level
with the number field universe free. The dense subset consists of fixed
smooth vectors whose Hilbert values are canonical images of original
fixed vectors. `fixedLevelDensity` proves the statement.
