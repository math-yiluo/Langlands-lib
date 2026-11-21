# Rational sections from central scalar numerators

An order-linear local presentation consists of an actual isogeny numerator whose rational image is the original section multiplied by a power of a natural number `p`. The central action is structural on the tangents of both formal module laws. `centralNumerator` keeps the same integral map with these central laws. `centralSection` scales its rational image by the inverse of the scalar power in the target field `K`. This uses the field's total inverse. At exponent zero it gives the numerator's image. If `p` vanishes in `K`, a positive exponent gives the zero section.

The overlap comparison assumes that the original scalar ring is a discrete valuation ring with fraction field `F`, that its image of `p` is irreducible, and that the source is divisible by that scalar. When the original sections agree on the overlap, faithful rationalization gives equality of the cross-scaled integral maps. A natural-number scalar power acts by the same coordinates on both scalar laws, so the centralized numerators satisfy the same cross multiplication equation. The hypothesis that `p` is nonzero in `K` allows cancellation to give equality of the centralized sections.

This is a construction for the order-linear rigidification of the primal summand in Rapoport–Zink 1996, (6.17) and Lemma 6.44, printed pp. 309–310 (PDF pp. 321–322).
