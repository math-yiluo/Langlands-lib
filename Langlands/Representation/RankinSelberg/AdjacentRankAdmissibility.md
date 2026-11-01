# Admissibility and closed fixed-vector coefficients for adjacent induction

This internal prerequisite uses the existing exact adjacent lower parabolic,
original-module inducing coordinates, generic admissibility transport, and
compact-quotient induction theorem. It introduces no literature-based definition.
The field and original module have independent universes, and every natural rank
is allowed.

The actual large-block projection of the opposite parabolic is continuous, open
and surjective. Continuity and openness follow by composing the opposite Levi
projection with evaluation at the first block. Surjectivity uses the diagonal
section of a Levi tuple whose first block is prescribed and other blocks are
identity.

For any continuous quasicharacter, admissibility of the original representation
passes to its pullback along this projection. Both determinant weights in the
compact-section formula have open kernels. Their pulled-back kernel intersection
lies in the kernel of their ratio, so this ratio is a smooth character.
Admissibility of its twist therefore follows from generic twist admissibility.
The existing original-module coordinates identify this action with the exact
tensor-valued normalized inducing action. Finally compactness of the actual
opposite-parabolic quotient and the generic compact-quotient induction theorem
prove admissibility of the canonical normalized opposite induction. No
irreducibility, Whittaker coefficient injectivity, or topology on the original
module is required.

`fixedCoefficientMap` is the linear map from vectors fixed by one open subgroup
to their scalar coefficient functions for a fixed linear functional. For an
admissible representation its source, and hence its range, is finite dimensional.
The function space has the ordinary product topology over the complex numbers;
its finite-dimensional subspaces are closed. The resulting limit theorem states
that pointwise limits of a sequence of coefficients of vectors fixed by the
same subgroup remain coefficients of a vector fixed by that subgroup. Only the
function target is given a topology. No continuity of the functional, topology
on the representation module, or injectivity of its coefficient map is assumed.
This prerequisite does not yet identify the whole Schwartz model image.
