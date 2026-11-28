# Restriction of visible twisted characters to a fixed Hecke corner

Fix a compact open subgroup of a Hausdorff locally compact totally disconnected
group with its Borel structure and a supplied Haar measure. The inverse twisting
automorphism sends the subgroup into itself.
Call a representation visible at this subgroup when it has a nonzero fixed
vector. On any finite family of visible irreducible admissible twisted pairs,
an arbitrary test has the same traces as a test bi-invariant under the subgroup.

Choose one representative from each equivalence class in the finite family.
The compact-open corner interpolation theorem matches the traces on these
representatives. Schur's lemma makes the traces from equivalent representations
proportional even with independently chosen twisting isomorphisms, so the
same test matches the whole family. Each linear combination of visible traces
uses a finite family. The trace comparison proves
`HeckeCornerRestrictionStatement`, the injectivity of restriction to the
bi-invariant tests on the span of any set of visible twisted traces.

A separate vanishing lemma uses the image of the integrated action of a
bi-invariant test. That image lies in the fixed space, so it is zero if the
fixed space is zero. The resulting trace vanishes for every twisting
endomorphism.

Arthur–Clozel (1989), Chapter 1, Lemma 6.3, obtain independence of two twisted
characters by using the simple modules of a common Hecke corner. The Lean
argument uses finite-family interpolation on that corner to preserve all
relations among the visible traces. The vanishing at zero fixed space is
the test-function counterpart of the domination condition on functionals
in Henniart–Lemaire (2011), II.5.7, Remarque (1).
