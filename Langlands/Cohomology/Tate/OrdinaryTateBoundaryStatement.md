# Ordinary-to-Tate cocycles and connecting maps

Author: Worker 45.

`Langlands.Tate.OrdinaryTateBoundaryLaws` states two compatibility properties
of the published canonical map `ordinaryToTate` from ordinary group cohomology
to Mathlib's actual Tate cohomology. It quantifies over a commutative ring `R`,
a finite group `G`, and representations in an arbitrary common universe `u`.

The first clause concerns every natural degree `n`, including zero. An ordinary
cocycle `z` is a cochain whose differential vanishes. The comparison sends its
ordinary homology class to `cycleClass (tateComplex A) n z hz`, the class of the
identical cochain in the actual Tate complex. The nonnegative cochain objects
and differentials are definitionally those of the ordinary inhomogeneous complex.
At zero this asserts compatibility with the norm quotient, not an isomorphism.

The second clause concerns every short exact sequence of representations
`0 → S.X₁ → S.X₂ → S.X₃ → 0` and every natural degree `n`. It asserts
`ordinaryToTate ∘ δordinary = δTate ∘ ordinaryToTate` as an equality of
`R`-linear maps from ordinary degree `n` of `S.X₃` to Tate degree `n + 1`
of `S.X₁`. Both connecting maps are Mathlib's actual connecting maps.
This includes the zero-to-one boundary and has no splitting, projectivity,
or tensor exactness assumption.

This is an internal compatibility target for the published comparison
construction. Its mathematical normalization is Serre, *Local Fields* (1979),
Chapter VIII, §1, printed pp. 127–129 (PDF pp. 133–135): the degree-zero Tate
group is invariants modulo norms, the positive groups are ordinary cohomology,
and these groups form the spliced cohomological functor. The explicit
inhomogeneous-cocycle formula and the commutative-ring linear formulation are
internal specifications of those identifications, rather than quotations of a
separately numbered theorem. This file states the properties; it supplies no
proof and makes no ordinary cup-product comparison claim.
