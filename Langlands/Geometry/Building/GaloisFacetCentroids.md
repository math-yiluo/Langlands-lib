# Canonical fixed centroids of invariant full facets

This internal result concerns the actual coefficient action on the original
quotient of supplied integer-valued KP apartment data over a field extension
`K/k`. The supplied data include coefficient stability, connected reductivity
over `K`, a maximal split torus there, the actual centralizer datum and full V6.
The additional premise is that the actual affine roots form an affine root
system admitting rank zero. The result imposes no local-field, topology or
apartment-axiom hypothesis.

The published preservation and reflection of membership in the full affine-root
set under `galoisAffineFunctional` puts the inverse coefficient affine action in
the actual root stabilizer. Closure under inverses puts the coefficient affine
action there as well. The published
`AffineRootSystem.facetCentroid_apply_of_mem_rootStabilizer` then proves
equivariance of the original affine centroid. To pass to the actual quotient, choose a
translated original apartment presentation of a facet. Semilinearity sends it
to the chart given by the coefficient conjugate of the rational point and the
coefficient image of the original affine facet. The all-chart computation in
`IntegerBuildingFacetCentroids` then proves equivariance of quotient centroids.

`IsGaloisInvariantFacet` means literal equality of the full-facet subset with
its image under every actual coefficient permutation. Such invariance fixes
the canonical centroid by the preceding equivariance. The centroid belongs to
the original open facet, so this supplies a fixed point there. Conversely the
published facet partition and coefficient action show that a full facet meeting
the fixed locus is invariant. Thus the existing `IsGaloisFacet` predicate is
equivalent both to invariance and to fixedness of the canonical centroid.

The centroid of every existing Gamma-facet lies in its actual fixed part.
The equivalence `galoisFacetEquivInvariant` retains exactly the same underlying
full facet in both directions; only its property proof changes.
`GaloisFacetCentroidsStatement` collects the two predicate equivalences.
All constructions work in arbitrary universe and either characteristic,
including rank zero.

The provenance is the explicit internal deduction above from the published
coefficient root transport, semilinear quotient action, and facet partition,
using the supplied integer-building centroid construction. No building descent
statement is used. This proves neither the affine-root-system premise nor
residue parabolic correspondence, residue descent, torus lifting or the host
prescribed-point split-torus theorem.
