# Closed-ideal effectiveness on finite full-domain covers

The theorem `idealEffectiveness` proves the unchanged
`Domain.FiniteCover.IdealEffectivenessStatement` by composing the proved
strict rational ideal theorem, strict scalar-normalization reduction, and
full-domain rational-refinement reduction.

The strict theorem is established through the actual binary Laurent split
square, bounded overlap splitting and density, approximation inside closed
ideals, finite iterated Laurent and all-unit standard refinements, and the
standard-cover induction on tuple length and nonunit entries. Finite standard
rational refinement recovers every strict rational cover. Its global ideal is
the explicit intersection of inverse images.

The scalar-normalization theorem transfers the entire strict ideal theorem
back to the original complete ultrametric field and arbitrary positive
polyradii. It realizes the base, chart and overlap radii in one complete field
extension, together with an extra radius `2` that ensures a nontrivial norm.
Original local ideals are extended and closed in the normalized strict chart
algebras. Commuting actual overlap maps preserve compatibility, so the strict
theorem applies.

A bounded coefficient retraction sends the strict contracted ideal into the
original explicit contraction. For each original local ideal, linearity of the
chart retraction and density of fractions in the normalized chart show that
the original local ideal lies in the closed extension of that contraction.
The opposite containment follows from the closed-extension adjunction. This
descends the actual local ideals, not only their scalar sections. The scalar
theorem takes the strict theorem as its argument, so no strict-effectiveness
premise remains in the final theorem.

The full-domain reduction takes the published actual relative rational
refinement over the containing domain's algebra. Closed extension transports
the original compatible ideals to that refinement. Actual intersection tests
prove compatibility there, and ideal locality proves equality of the refined
and original contractions. Rational effectiveness and locality on the
original-component intersection covers prove the reverse ideal containment
on each original covering domain. The elementary containment is already
provided by the closed-extension adjunction.

Thus every original local ideal is exactly the closed extension of the
prescribed explicit contraction along the original actual restriction map.
No global ideal witness or reverse containment is supplied as an additional
hypothesis. The proof retains trivial coefficient valuations, arbitrary
positive radii, nonreduced and zero algebras, empty spectra and empty finite
covers.

The source motivation is Berkovich, *Etale cohomology for non-Archimedean
analytic spaces* (1993), Kiehl's Theorem, its strict-to-general reduction and
Remark 1.2.1(ii), printed page 15 / PDF page 12. The registered source is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The implemented proof is the ideal-specific Library argument described above,
rather than an invocation of an unproved finite-module descent theorem.
