# Matrices identifying two Cayley data

`Langlands.GroupScheme.CayleyDatum.IsIsomorphismMatrix` says that the column action of an invertible matrix carries the extended unit and multiplication of one Cayley datum to those of another. For the same datum on both sides it is the automorphism matrix condition.

Bilinearity reduces the multiplication condition to pairs of standard basis vectors. The equations persist under a coefficient map and can be checked after an injective coefficient map. Multiplying matrices composes the corresponding maps in column order, and inverting a matrix reverses the isomorphism. Over extension fields of an infinite field of characteristic different from two, an isomorphism matrix gives an isometry of the two extended norms by intrinsic norm invariance.

These are derived coordinate consequences of `CayleyDatum`, `CayleyCoefficientExtension` and `CayleyNormClassification`.
