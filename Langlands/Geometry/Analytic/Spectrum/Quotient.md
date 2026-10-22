# Proof of the closed-ideal quotient spectrum theorem

Author: Worker 36.

`Langlands.Analytic.quotientSpectrumProperties` proves the separate proposition
`Langlands.Analytic.QuotientSpectrumStatement`. The original module path also
retains the named descent construction and its image and embedding lemmas.

The zero locus is the intersection of the closed zero fibers of all ideal
elements under the continuous evaluation maps. A multiplicative seminorm
annihilating the ideal is constant on additive cosets by two applications of
the triangle inequality. `descend` therefore defines it on the actual ring
quotient. Multiplicativity and the seminorm laws descend by representatives.
Every quotient element has a representative of norm less than its quotient
norm plus any positive epsilon. Applying the original bound and letting
epsilon decrease to zero proves the descended norm bound.

Surjectivity of the quotient projection proves injectivity of spectrum
pullback and uniqueness of descent. Pullback is continuous, the quotient's
spectrum is compact, and the original spectrum is Hausdorff, so this injection
is a closed embedding. Vanishing of ideal elements proves one image
inclusion; the constructed descended point proves the other. The closing
theorem collects these results, and quotient representatives identify the
unique seminorm asserted in the final clause.

The proof uses the separate general spectrum-properties results and Mathlib's
actual ideal quotient and quotient norm. It does not require completeness or
ultrametricity, and does not prove spectrum nonemptiness or analytic-domain
representability. Source conventions and the derived scope are recorded in
the paired Quotient/Definitions and Quotient/Statement Markdown. The primary
source is Berkovich's Trieste 2009 lectures, Definitions 1.2.3 and 1.2.5 p.4
and the opening quotient-norm paragraph of §2.1 p.7.
