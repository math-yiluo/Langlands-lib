# Strict scalar normalization for rational ideal effectiveness

This module states two unproved propositions. It supplies neither an axiom
nor a proof of either proposition.

`StrictRationalIdealEffectivenessStatement` is the closed-ideal specialization
of Kiehl effectiveness for the Library's actual strict rational data over a
complete nontrivially normed ultrametric field. The nontrivial valuation
condition is explicit as the existence of a coefficient with norm greater
than one. The local ideals have equal closed extension along the two actual
strict rational intersection restrictions. The conclusion identifies every
local ideal with closed extension of the explicit intersection of inverse
images in the base algebra.

`StrictScalarIdealDescentStatement` states that the entire strict theorem
implies the general finite rational ideal-effectiveness theorem, including
arbitrary positive radii and trivial original coefficient valuations. The
general target keeps the original actual quotient norm topologies and the
explicit global contraction. No original-field reverse containment,
effectiveness or global ideal witness is an extra premise.

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), Kiehl's Theorem, the ensuing strict-to-general reduction paragraph and
Remark 1.2.1(ii), printed page 15 / PDF page 12. Berkovich states compatible
finite-module effectiveness and its equalizer identification, and explicitly
reduces the arbitrary-radius and trivial-valuation case to the nontrivially
valued strict case by Berkovich (1990), §2.1 (2.2.5 and 2.1.11).
These propositions are derived ideal specializations, rather than a claim
that the source uses the Library's implementation of quotient norms.
The registered source is `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The Library already constructs finite radius realizations with a bounded
coefficient retraction, strict scalar extension with a module-linear
retraction, normalization of rational charts and overlaps, and additive
retraction from the normalized strict charts. These are available proof
infrastructure. Their scalar equalizer descent does not by itself prove the
ideal reduction stated here.

Both effectiveness propositions allow nonreduced and zero algebras, empty
spectra, and empty finite rational covers. The scalar reduction is separate
from the remaining proof of the strict rational theorem, and from the
published reduction of general full-domain effectiveness to general rational
effectiveness.
