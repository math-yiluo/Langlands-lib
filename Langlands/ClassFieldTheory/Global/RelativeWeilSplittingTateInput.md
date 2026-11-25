# Tate acyclicity of the relative Weil splitting representation

Let `F` and `E` be number fields in `Type u`, with `E/F` Galois, and let
`c` be a global class family. `splittingRepresentation c F E` is the actual
twisted splitting representation of the normalized representative chosen by
`ClassExtension.representative (c F E)`. This is the same representative used
to define `RelativeWeilGroup c F E`, and its coefficient action is the actual
relative Galois action on the idele class group of `E`.

`splittingRepresentation_tate_isZero` assumes `FundamentalClass.Generates c`
and `FundamentalClass.Restriction c`. The global idele-class Tate theorem
gives bijectivity of integral cup by `c F E` in every integer degree.
The chosen representative has exactly this ordinary second cohomology class,
by `ClassExtension.cohomologyClass_representative`. The concrete
splitting-module theorem therefore proves Tate acyclicity of this
representation in every integer degree.

The provenance is internal, by specialization of the global cup input and
the computed splitting-module class. The local invariant assumptions,
inflation and local compatibility of the eventual reciprocity target are
not needed for this conclusion. Transfer and its commutator kernel are
separate remaining comparisons.
