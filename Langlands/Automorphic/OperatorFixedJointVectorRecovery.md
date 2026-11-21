# Recovery at a fixed finite level

An open subgroup fixing a vector in the Hilbert completion witnesses
smoothness for the completed finite action. If the vector's compact orbit
also spans a finite-dimensional subspace, the supplied joint vector recovery
gives its preimage in the original carrier. Equivariance and injectivity of
the canonical map show that the preimage remains fixed by the same open
subgroup. The lemma is an internal specialization of `JointVectorRecovery`.

`fixedSmoothImage` records the portion of the ambient fixed smooth space
whose underlying Hilbert vectors have an original fixed preimage. Given
density of compact-finite smooth vectors at that level and agreement of
the finite actions, fixed vector recovery puts that dense set inside
`fixedSmoothImage`.
