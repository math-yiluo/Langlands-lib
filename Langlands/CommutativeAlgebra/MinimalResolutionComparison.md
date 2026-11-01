# Split comparisons with minimal free resolutions

This internal infrastructure gives the local algebra argument needed to compare
a Koszul complex with the iterated minimal covers. It is derived from the
companion construction, quotient tensor products, and Mathlib's local splitting
criterion.

The definition `minimalResolutionComparison` constructs compatible comparison
maps from any complex of projective modules augmented to the given finite
module. Exactness of the source complex is not required. First lift its
augmentation into the degree-zero cover. In the next degree, the preceding map
composed with the source differential lands in the kernel of the preceding
cover. This gives a map to the next syzygy, which lifts to its free cover by
projectivity. The equation that the source differential squares to zero supplies
the next cycle condition. Induction gives all degrees, with the declared
augmentation and differential compatibility equations.

For a linear map between modules, if the preimage of the maximal-ideal multiple
of the target is contained in the maximal-ideal multiple of the source, the map
becomes injective after tensoring with the residue field. Every element of that
tensor product is represented by `1 ⊗ x`; its vanishing is precisely membership
of `x` in the maximal-ideal multiple. For a finite source and finite free target,
the local splitting criterion then supplies a linear left inverse.

Suppose a sequence of finite source modules maps compatibly into the successive
free modules of the minimal resolution, and its map in degree zero splits. Also
suppose its differential has the following detection property: if the image of
an element lies in the square of the maximal ideal times the preceding source,
that element lies in the maximal ideal times its own source. All comparison maps
then split, by induction. The target differential carries a maximal-ideal
multiple into its square by minimality. A left inverse in the preceding degree
transports this containment back to the source, where detection and the local
splitting criterion prove the next step.

Under `HasProjectiveDimensionLT M n`, the free module in degree `n` is zero.
For `n = 0` this follows from the zero-object criterion and minimality; for a
successor it follows from the companion syzygy-stopping result and minimality.
A nonzero module split into that degree therefore proves `n ≤ pd(M)`.

Combining these results, `projectiveDimension_ge_of_projectiveComplex` gives the
bound in every nonzero degree of a complex of finite projective modules whose
augmentation becomes injective over the residue field and whose differential
has the detection property. The residue-field injectivity of the augmentation
implies that of the degree-zero comparison by its lift equation, establishing
the base split injection.

The module does not by itself supply a Koszul differential or prove its detection
property, and it does not yet prove the residue-field lower bound.
