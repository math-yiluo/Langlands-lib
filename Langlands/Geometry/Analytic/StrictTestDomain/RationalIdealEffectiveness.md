# The strict rational ideal correspondence

This module constructs the order isomorphism between global ideals of a
presented strict affinoid and compatible ideal families on any finite
rational point cover over a complete nontrivially valued ultrametric field.
Its inverse is the explicit intersection of inverse images under the
original rational base maps. It also proves the exact
`StrictRationalIdealEffectivenessStatement`.

The source motivation is the ideal specialization of Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), Kiehl's
Theorem and Remark 1.2.1(ii), printed page 15 / PDF page 12. The registered
source is `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The implemented proof is assembled from independently developed Library
and supporting constructions, and does not invoke an unproved Kiehl or
finite-module descent premise.

The binary Laurent theorem comes from the explicit split square of bounded
algebra maps. Its bounded overlap splitting, density, scalar gluing,
Noetherianity and closed ideals establish the two-member ideal theorem by
the approximation proof in `SplitSquareIdealDescent`. Actual bounded
diagram comparisons transport it to the strict rational upper and lower
domains.

Induction over the number of Laurent splits, using coefficient-pullback
refinements and the proved Laurent ideal chase, gives effectiveness on
finite iterated Laurent covers. The actual pairwise-ratio Laurent
refinement gives the all-unit standard rational case. The standard-cover
induction then uses a scalar threshold and an upper/lower split to decrease
the tuple length on the upper branch or the number of nonunit entries on
the lower branch. The finite standard rational refinement theorem
recovers effectiveness on every original finite rational cover.

This supplies `idealCoverDescent_finiteRational`, with all analytic inputs
discharged. The previously proved quotient-based ideal-locality theorem
identifies contraction of global closed extensions with the original
ideal and detects the inclusion relation. Together these give the
left inverse, right inverse and order laws of `rationalIdealOrderIso`.
The final theorem unfolds the exact strict proposition and applies the
proved finite rational effectiveness.

All algebras, norm topologies and maps are the actual stored ones. The
proof retains nonreduced and zero algebras, empty spectra, and empty finite
rational covers. The nontrivial coefficient valuation is explicit here;
the separate scalar-normalization reduction is still needed for the
general-radius, possibly trivially valued full-domain target.
