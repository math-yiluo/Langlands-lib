# Canonical centroids for integer-valued building facets

This internal construction extends the published local-field construction in
`BuildingFacetCentroids` to the actual quotient of supplied
`IntegerValuationBuildingData` over an arbitrary field. It retains the explicit
premise that the actual affine roots form an affine root system admitting rank
zero. It assumes no topology, local compactness, or apartment axioms.

The finite actual relative roots give the existing root-coordinate norm on the
reduced translation space, and their injective coordinate map gives finite
dimensionality. The canonical affine centroid is the published
`AffineRootSystem.facetCentroid`, averaging all actual incident vertices in the
original affine torsor. The empty root system on a point is included.

Choose an original translated-apartment presentation of a full facet and map
its affine centroid into the original quotient. To prove that every presentation
gives the same point, use the actual quotient relation to compare two charts at
a shared point. The published integer-building normalizer comparison agrees on
the entire original closed facet, with no apartment-axiom premise. The centroid
belongs to its original open facet and hence to that closed facet. The normalizer
preserves the entire affine-root set and therefore commutes with the affine
centroid. Finally the affine centroid is constant on each original facet. These
facts prove chart independence without invoking chart injectivity.

The quotient centroid lies in its original open facet. Taking its containing
facet recovers that same facet, so centroids distinguish full facets. Translating
a presentation also proves equivariance under actual rational group points.
`IntegerBuildingFacetCentroidsStatement` collects membership, the left inverse,
and injectivity, with precisely the explicit affine-root-system premise.

The provenance is this internal deduction from the published affine-centroid,
root-coordinate metric, and integer-building facet comparison APIs. It constructs
neither building data nor an affine-root-system proof, and does not prove residue
parabolic geometry, torus lifting, or the host split-torus theorem.
