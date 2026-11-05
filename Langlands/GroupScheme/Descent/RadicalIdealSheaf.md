# Defining-ideal descent of a represented radical

This internal adapter identifies the radical inclusion's full defining ideal
on the affine base change with its kernel on global sections, expressed in the
actual tensor coordinates of a chosen affine presentation. Mathlib's
`Scheme.ker_of_isAffine` gives the section-kernel identification; contraction
along `sectionsEquiv` then gives `coordinateIdeal`.

For an arbitrary Galois extension, the already proved coefficient-conjugation
stability and ground-section projection formula discharge both compatibility
premises of `AffineIdealDescent.ofGaloisStableTensorIdeal`. The result
`idealSheafDescent` constructs an actual ideal sheaf on the original ambient
scheme whose pullback is the radical inclusion's defining ideal sheaf.
The closed-subgroup ideal criterion consequently proves equality of the two
actual subgroup images over the double overlap, retaining every relative test
scheme and the full ideals.

The affine presentation is supplied, and the radical is represented by a
supplied inclusion satisfying `IsUnipotentRadical`. This module does not
construct a radical or prove the final perfect-field equivalence. There is
no finite-degree, finite-generation, characteristic or reducedness hypothesis.
Worker 1370 authored the radical coordinate bridge; Worker 1359 authored the
reused defining-ideal and affine ideal-sheaf descent adapters.
