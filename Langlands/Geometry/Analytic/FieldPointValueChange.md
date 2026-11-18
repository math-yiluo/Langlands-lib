# Isometric change of value field for full analytic points

Over a complete ultrametric normed field `K`, `FieldPoint.mapValue`
postcomposes the chart evaluations of a full analytic point with a
norm-preserving `K`-algebra map between normed extension fields. The underlying
point and the chart seminorms stay fixed. Postcomposition preserves the
evaluation identities for chart restrictions.

`FieldPoint.eq_mapValue_of_point_eq` identifies every extension-valued point
above the underlying point of a full `K`-valued point with its scalar image.
In each containing chart, injectivity of the chart embedding identifies the
two spectrum points. For an element `a` of the chart algebra, subtract the
scalar given by its `K`-valued evaluation. The difference has norm zero under
both evaluations, so the extension-valued evaluation of `a` is the image of
its `K`-valued evaluation. Extensionality gives equality of the full points.

The object equivalence for localization gives the corresponding uniqueness
of extension-valued points on a localized object. The same module records
the naturality of the underlying-point projection after removing the
universe lift.

## Provenance

These are internal deductions from the published full field-point structure,
the atlas chart embeddings, and the natural projection on the localized
category. The scalar-subtraction argument extends the chart-level uniqueness
argument in `FieldPointSaturationComparison` to normed extension fields over
a base-field point.

`mapValue` applies the existing field-point map after converting norm preservation to isometry. [Field-point transport](CommonPointField/Transport.md)
