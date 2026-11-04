# Coordinates selected from a rational orbit

This internal helper chooses a basis from a spanning set while keeping a
specified nonzero generator. It uses basis extension inside the span,
reindexes the finite basis by `Fin d`, and splits its inclusion into the
ambient coordinate space.

For a matrix representation, the rational orbit span of a coordinate vector
is preserved by every rational matrix, since products of rational points
give products of matrices. The selected split coordinates then satisfy the
invariance equation on rational points. Rational detection promotes that
equation to every test scheme when the group is reduced and locally of
finite type over an algebraically closed field.

The module defines `rationalOrbitSpan` and proves that each rational matrix
preserves it. The theorem `exists_rationalOrbit_coordinates` supplies a finite
index `Fin d`, split matrices `B` and `C` with `C * B = 1`, orbit-vector
columns, all-test invariant coordinates, and a column equal to the original
coordinate vector.

These are internal constructions derived from Mathlib basis extension and
the existing rational-coordinate detection helper. They are prerequisites
for the normal-kernel argument and do not prove the quotient theorem.
