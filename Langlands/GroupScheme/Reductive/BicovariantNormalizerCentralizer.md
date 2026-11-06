# Bi-covariance and the actual maximal-torus centralizer

This internal construction works over an arbitrary field `k : Type u` with an
actual connected reductive group, an actual split maximal torus, and a supplied
finite root datum on that torus's actual character and cocharacter lattices.
The root index type is in `Type u`, as required by the published exact Weyl
comparison. No structural subgroup or root datum is asserted to exist.

The torus embedding factors through two supplied affine groups. Supply a
rational character on each, opposite restrictions to this same torus, and an
ambient coordinate left covariant for the first character and right inverse
covariant for the second character on every relative test scheme. Assume that
the first restricted character pairs nontrivially with every supplied coroot.

For a rational normalizing point where the coordinate has a unit value,
`mem_centralizerPoints_of_unit_bicovariant` proves membership in the actual
torus centralizer. The companion bi-covariant character theorem fixes the
actual restricted integral character. The exact published `weylGroup` theorem
identifies the full integral normalizer image with the supplied root datum's
Weyl image. The published regular-weight centralizer criterion then uses
integral polarization and the generic-cocharacter centralizer theorem to
deduce centralization.

`centralizerPointOfUnitBicovariant` constructs the point of the actual
centralizer, and its value theorem identifies its ambient point with the
original supplied normalizing point.

The proof retains the actual supplied torus, root datum, characters,
factorizations, covariance laws and regularity certificate. It proves no
existence of these data, makes no assertion that the centralizer equals the
torus, and supplies no Bruhat factorization or Steinberg irreducibility.
Its provenance is the implemented internal composition of the companion
character theorem and the published Weyl-image and regular-weight centralizer
results.
