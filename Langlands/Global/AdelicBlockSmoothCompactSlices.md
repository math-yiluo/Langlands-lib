# Smooth compact slices of realized scalar adelic sections

`compactPair` pairs the actual infinite and finite standard compact elements. `HasSmoothCompactSlices` is the condition that, for each fixed finite compact point and each fixed adelic Levi point, the normalized slice as a scalar function of the infinite compact point has local smooth extensions in the mixed matrix coordinates.

`exists_smoothCompactSlice_expansion` applies this condition to a compact-finite section. At a fixed finite compact point, the normalized slices lie in the image of the finite-dimensional infinite compact orbit span under evaluation at the compact point whose infinite component is the identity. This image consists of actual scalar Levi coefficients.

On any finite-dimensional subspace of scalar functions, point evaluations have zero common kernel, hence span the algebraic dual. Each coordinate of a basis of the slice image therefore has a local smooth extension by finite linear combination of the supplied scalar extensions. The basis expansion, evaluated on the compact points in a common neighborhood, uses the same finite family of actual Levi coefficients throughout.

This internal argument uses the algebraic dual annihilator theorem and the actual compact action on the scalar section carrier. The scalar compact model comes from Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283).
