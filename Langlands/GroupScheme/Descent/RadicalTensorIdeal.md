# Tensor coordinates of a represented radical

This internal adapter uses the actual affine presentation of a group scheme
over a field and the tensor coordinates constructed in `TensorCoordinates`.
`groundSectionsEquiv` identifies the original affine algebra with the original
scheme's global sections. The first projection of field base change induces
the inclusion `a ↦ 1 ⊗ a` under these equivalences. Naturality of
`Scheme.ΓSpecIso` and the proved spectrum comparison identify the canonical
semilinear scheme map on global sections with coefficient conjugation.

For an actual represented unipotent radical of the field base change, the
source isomorphism `IsUnipotentRadical.galoisSourceIso` gives a semilinear
self-map of the radical scheme. Its square with the actual inclusion commutes:
this follows from the characterizing inclusion square of that source
isomorphism and the two pullback projections of the canonical ambient descent
comparison.

`coordinateIdeal` is the kernel of the radical inclusion on global sections
after the tensor-section ring equivalence. Applying global sections to the
commuting semilinear square proves stability of this kernel under every
coefficient conjugation. The earlier infinite-Galois ideal-descent theorem
then identifies it with its contraction to the original affine algebra
extended back to the tensor algebra.

The coordinate comparisons and stability require no Galois hypothesis; only
the final contraction-extension equality assumes `IsGalois k K`. There is no
finite-extension, reducedness, characteristic or finite-generation hypothesis.
This adapter neither constructs a radical nor claims effective subgroup
descent or the final perfect-field equivalence.
