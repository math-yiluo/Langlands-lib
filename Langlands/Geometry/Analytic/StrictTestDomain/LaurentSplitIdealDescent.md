# Ideal descent across a Laurent split

This is an internal conditional reduction for the strict rational
effectiveness proof. `BinaryIdealDescent` is a proposition defining the
two-member effectiveness input: compatible ideals on the two specified
actual rational domains are the closed extensions of some global ideal.
This module does not prove the binary analytic theorem.

`laurentSplitIdealDescent` assumes this binary theorem for the upper and
lower Laurent domains of a function, together with effectiveness for the
original rational family after coefficient pullback to each branch.
It concludes effectiveness for the original finite rational point cover.

Given compatible ideals, extend them by the actual comparison maps to each
branch and form their explicit contractions there. Branch effectiveness
recovers these local extended ideals. On the actual upper/lower overlap,
test the two branch contractions with the original rational cover pulled
back to that overlap. The actual coefficient triangle maps and composition
of closed ideal extension identify both test extensions with the same
transported original ideal. Ideal locality therefore gives binary
compatibility of the branch contractions.

The assumed binary theorem supplies a global ideal with these branch
extensions. For each original covering algebra, the actual pullback-swap
map transfers the branch equations to its own pulled-back binary Laurent
cover. Ideal locality on this binary cover recovers the original ideal
as the closed extension of the supplied global ideal. Finally, ideal
locality on the original finite rational cover proves that this global
ideal equals the explicit intersection of inverse images. The conclusion
therefore uses the prescribed contraction, rather than an extra global
ideal witness hypothesis for the original family.

The coefficient field's nontrivial valuation is explicit and is used by
the strict ideal-locality theorem. Nonreduced and zero algebras, empty
spectra, and empty finite rational covers remain included. The argument
is derived from actual coefficient triangle and swap maps, elementary
closed-extension composition, and the proved ideal-locality theorem.
