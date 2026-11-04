# Proof of the affine-line correction to Conrad's Remark 3.3

This proof establishes the exact target
`Langlands.AlgebraicGeometry.PointTopology.ConradRemark33Correction`.
Its source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed page 5, Remark 3.3, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The distinction between nilpotent support and zero-subscheme factorization
is a derived correction, as explained in the statement's Markdown.

For an arbitrary commutative ring R, evaluation at zero on R[t] has kernel
(t). The implemented proof shows by polynomial induction that every p
differs from its constant evaluation by an element of (t). Surjectivity
of evaluation and Mathlib's range theorem for comap on prime spectra
then identify the underlying image of the actual zero section with V(t).

For any commutative R-algebra S, the underlying map of the point with
coordinate s is prime-spectrum comap of evaluation at s. Its whole image
lies in V(t) exactly when every prime ideal of S contains s. Mathlib's
nilradical theorem identifies this condition with nilpotence, including
the zero-ring case. No topology or locality is used.

`affineLineStratificationProperties` assembles the six clauses. The
underlying complement identity follows from the image V(t) and the
definition of D(t). The existing exact point-range theorems for the
origin and puncture give the zero and unit conditions. For nontrivial
S these are disjoint because zero is not a unit. Surjectivity of the
actual coordinate equivalence proves that their union covers exactly
when every element of S is zero or a unit. All other clauses allow
the zero ring. R and S lie in the same arbitrary universe as in the
target; there is no topology, faithfulness or locality premise.

`conradRemark33Correction` proves the combined statement. In a field,
every nonzero element is a unit, giving the field coverage clause over
any commutative base ring acting on that field.

For the counterexample the base and value ring are both the actual
dual-number ring K[epsilon], for an arbitrary field K. The point is
exactly the inverse of the actual coordinate equivalence at epsilon.
Mathlib provides locality and nilpotence of epsilon, and
`dualNumber_isArtinianRing` provides Artinianness. The nilpotent-image
criterion places its whole underlying image in the origin. The exact
zero and unit point ranges, together with the existing nonzero and
nonunit epsilon laws, show that this same point factors through neither
stratum. Thus the proof distinguishes underlying image containment from
closed-subscheme factorization and establishes the stated correction
to a coverage reading of the local Artinian sentence. This focused
result does not assert general closed/open coverage or whole-paper
completion.
