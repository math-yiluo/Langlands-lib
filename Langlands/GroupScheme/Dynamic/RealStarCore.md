# A polynomial adjoint core containing a real cocharacter

Author: Worker 1655.

This internal construction provides a polynomial adjoint-stable subgroup
of an actual extension image containing all values of a specified real
cocharacter. Coefficient fields have arbitrary universe `u`; the matrix
index is a finite type in `Type`.

`starCore H` consists of the elements of a matrix subgroup `H` whose
adjoints also belong to `H`. It is a subgroup because adjoint reverses
multiplication and commutes with inversion. Adjoint preserves this core,
and every adjoint-stable subgroup of `H` is contained in it.

`transposeMatrix` transposes a matrix unit and its inverse. It commutes
with scalar extension. On the matrix and inverse-matrix coordinate
families, transpose swaps the row and column indices.

Vanishing at all units detects a Laurent polynomial over an infinite
field. The proof multiplies by a suitable power of the Laurent coordinate
to obtain an ordinary polynomial. Its evaluation vanishes at every
nonzero field element, an infinite set. The polynomial root bound makes
it zero, and multiplying back by the inverse Laurent monomial makes the
original Laurent polynomial zero. Evaluating the universal cocharacter
matrix at an extension unit recovers the actual cocharacter value, by
the previously established naturality at the universal Laurent unit.

For a closed representation, suppose that scalar conjugation fixes the
extended base coefficients. The actual image is the zero locus of its
base-field embedding ideal. Its equations are therefore preserved by
entrywise scalar conjugation. Applying this to the adjoint or transpose
of a matrix proves equivalence of adjoint membership and transpose
membership in that image. The core is consequently polynomially defined:
use the union of the original image equations and their transpose
renamings. The proof verifies both directions of this equation
description.

Now assume that the base field is `RCLike` and every base element is fixed
by conjugation. Assume adjoint stability of the actual base-field
representation image, and supply an actual cocharacter into that group.
Every base-field cocharacter value belongs to the image; its transpose is
its adjoint and belongs too. Evaluating each embedding equation at the
transpose of the universal Laurent cocharacter matrix thus gives a
Laurent polynomial vanishing at every base-field unit. Laurent detection
makes it zero. Extending this universal equation to any `RCLike` test
algebra proves membership of every transpose cocharacter value in the
actual extension image.

In a compatible scalar tower over the real numbers, fixedness of the
base elements also gives fixedness of their extensions. The adjoint and
transpose membership comparison then proves
`cocharacterUnitsHom_mem_starCore`: all extension values of the chosen
cocharacter belong to the polynomial adjoint core. No adjoint stability
of the full extension image is assumed.

The provenance is internal: the construction uses exact polynomial
equations for the actual closed representation image, cocharacter
naturality, and the ordinary polynomial root bound. It establishes the
subgroup and cocharacter-membership tools for real internal
unitarization. It does not yet construct the final base-field
conjugator from the core, an initial ambient realization, or a compatible
Iwasawa compact. The unconditional host statement remains open.
