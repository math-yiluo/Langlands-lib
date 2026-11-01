# Degree-zero scalar Laurent diagram chase

`laurentSplitScalarDescent.{u,v}` proves the exact
`LaurentSplitScalarDescentStatement.{u,v}`. It retains all three premises:
descent for the upper and lower pullback families and separation for the
overlap pullback family. It uses the published unconditional
`binaryLaurentGluing` and the proved actual quotient transport in
`ScalarCoverDescent`. It adds no analytic hypothesis.

Starting with compatible original sections, the proof sends them along each
actual quotient comparison to the upper and lower bases. Compatibility is
preserved by the actual intersection-comparison squares. The two descent
premises give unique lifts `aU` and `aL`.

The private `lift_eq_on_smaller` uses `pullbackTriangleMap` and its two squares
to send each lift equation to the actual upper/lower intersection base.
There the two restricted lifts have the same image under every member of
the pulled-back original family. The stated overlap separation premise
therefore makes them equal. Binary Laurent gluing on `P` yields a scalar
`a` with these upper and lower images.

For each original rational quotient, `pullback_base_images_eq` exchanges the
two actual rational bases using bounded extension. It shows that the image
of `a` and the given section have equal upper and lower images on that
quotient. The literal Laurent pullback identities identify these maps with
the binary Laurent base maps of the image of `f`. The helper
`eq_of_binaryLaurent_images`, derived from uniqueness in
`binaryLaurentGluing`, now shows that the original restriction equation holds.
Finally, any competing scalar has upper and lower images `aU` and `aL` by
the respective descent uniqueness premises. Binary uniqueness on `P` gives
equality with `a`.

This is the degree-zero implementation of the Laurent diagram chase
motivated by Achinger, *Introduction to non-Archimedean Geometry*, November
22, 2020, Lemma 7.3.3 and its application on pp.66–67. The exact original
and its fingerprint are recorded in the statement's Markdown. The
implementation uses only unique scalar lifting and separation, and makes
every required pullback comparison an actual proved bounded map.
Worker 146 contributed the formal compatibility and refinement preparation
used in `ScalarCoverDescent`; Worker 572 wrote this chase.

The field and index universes remain independent. No finite or point-covering
hypothesis is added, and the argument allows empty families, zero and
nonreduced bases, and empty rational loci under exactly the stated premises.
The result is conditional scalar degree-zero descent at unit radii. It
supplies a reduction for the standard-cover induction, with no claim of
higher exactness, admissibility, finite-module descent or arbitrary radii.
