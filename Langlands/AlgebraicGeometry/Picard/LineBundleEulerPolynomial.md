# Actual line-bundle Euler polynomials with the relative degree bound

This internal specialization of the coherent support theorem defines
`lineBundleEulerPolynomial f L d` by taking the structure sheaf as coefficient
module. The tensor left unitor identifies its twisted Euler sequence with the
actual Euler characteristics of `tensorPow L.obj n`. The statement includes every
natural exponent, including the structure sheaf at exponent zero.

The structure sheaf has finite affine sections because a ring is finite as a
module over itself. Tensoring it by an actual line bundle preserves finite affine
sections, and the tensor left unitor gives that property for the line bundle
itself. Proper coherent cohomology finiteness then gives finite cohomology for
every actual power on a proper scheme over any field.

If the scheme is noetherian and separated and its topological Krull dimension is
at most `d`, the coherent support induction and Newton reconstruction show that
this polynomial agrees with all of those Euler characteristics and has natural
degree at most `d`. The evaluation theorem accepts any finite-cohomology witness;
the Euler invariant does not depend on the choice of that proof.

The final corollary specializes to a scheme smooth of relative dimension `g`
and proper over a field. Properness supplies compactness and separatedness;
finite type over the field supplies local noetherianity. Thus the scheme is
noetherian. The published smooth topological dimension bound is at most `g`,
so the resulting polynomial has degree at most `g`. Geometric connectedness is
not needed for this degree upper bound.

The provenance is internal, using actual tensor unit comparisons, coherent
closure, proper coherent finiteness, the proved support induction, and the
existing smooth dimension theorem. The module does not prove the exact degree
or positive leading coefficient under ampleness.
