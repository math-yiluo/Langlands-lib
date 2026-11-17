# Centre and derived group of GL, and perfectness of its central quotients

`Langlands.GroupScheme.generalLinearCenterDerived.{u}` proves exactly the unchanged
published proposition `Langlands.GroupScheme.GeneralLinearCenterDerivedStatement.{u}`.
It holds for every field in universe `u`, every natural rank including zero and one,
and every fppf quotient by the full scheme-theoretic centre. The test schemes are
arbitrary, including non-affine and nonreduced schemes, and there are no added
hypotheses on the quotient.

The three supporting modules contain the following implemented arguments.

1. `GeneralLinearCenter` transports a central point through the matrix points
   equivalence into the centre of the invertible matrix group. Mathlib's
   `Matrix.GeneralLinearGroup.center_eq_range_scalar` supplies a unit scalar.
   Conversely, a point with scalar matrix factors through the actual scalar
   homomorphism, whose published centrality holds after every test restriction.
   The argument works over any commutative base ring, including empty index types.
2. `GeneralLinearDerived` identifies the range of the actual special-linear
   inclusion on every test scheme with determinant-one matrices and with the
   full determinant kernel. The representing isomorphism transports the kernel's
   closed immersion to this inclusion. All commutators have determinant one.
   For nonempty index type, published simple connectedness of SL includes
   semisimplicity, and the published perfectness of semisimple field groups makes
   SL perfect. Derived-subgroup functoriality then places every SL point in the
   derived subgroup of GL. Closedness and commutator containment give the reverse
   inclusion. For empty index type the SL point group is trivial on every test.
3. `GeneralLinearQuotientPerfect` proves perfectness of a central fppf quotient
   assuming that determinant-one GL points lie in its full derived subgroup.
   On an affine test, the published unit-root construction gives an fppf
   refinement on which the determinant has a root of order equal to the rank.
   Division by the corresponding scalar produces a determinant-one point. The
   scalar factor is killed by the full kernel identity, so the image of the
   original point lies in every closed commutator-containing subgroup after
   refinement, hence before refinement by effective-epimorphism descent.
   Zariski gluing extends the argument to arbitrary tests. Pulling the quotient
   map back along an arbitrary quotient point provides a lift after another
   fppf refinement and proves the desired total derived subgroup. Empty rank
   uses the identity point directly.

The final theorem combines the centre equivalence and the derived-group
identification, then discharges the quotient helper's determinant-one premise
with that identification. All new supporting Lean/Markdown pairs are included
in this contribution's repository paths, so the complete proof is reviewable
without relying on a separate unpublished result.

The inherited mathematical provenance is Milne, *Algebraic Groups* (2017),
Examples 6.22 and 12.47; the unchanged statement Markdown records the precise
source correspondence, low-rank conventions, quotient meaning, and errata.
The proof uses the published semisimple-perfectness theorem for the reverse
derived-group inclusion instead of repeating the source's elementary-matrix
argument.
