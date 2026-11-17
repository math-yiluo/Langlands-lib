# Common Weyl conjugation for the actual powered family

This internal supporting statement proves common Weyl-conjugation units
for genuine source maps and the actual powered target maps over a
commutative local ring. The source and target are affine group schemes
with closed coordinate tori and genuine normalized simple-root data.
Their root data have corresponding simple supports and positive systems,
and the target words are transported source words.

The original characteristic condition is retained: every target root
factor different from one implies `(p : R) = 0`. No additional target
conjugation law, rank-one law, partner-uniqueness premise or powered
parametrization property is assumed in `PoweredWeylConjugationStatement`.
`poweredWeylConjugation` proves that proposition in every universe; the
direct API is `weylConjugationRelations_powered`.

The earlier actual-family results supply braid, square, no-cone fixed,
A2/B2 signed and simple opposite-root identities. Genuine target
rank-one laws come from the published local opposite-pair theorem.
The actual source and target root data supply their standard coordinate
pairings, so no independent pairing premise occurs in the final statement.

For negative roots, reflection invariance identifies the four involved
root-power maps with one actual additive-line power map. Word transport
rewrites the assumed powered positive-conjugation identity in the
genuine target family. `PoweredNegativeConjugation` evaluates it at one,
uses genuine-root rigidity to recover the unit raised to the root factor,
and applies genuine negative conjugation. Precomposition converts its
inverse power to the desired inverse of the original arbitrary unit.
The correspondence of positive systems supplies the genuine target
positivity hypotheses.

These identities form every field of `TargetWeylRelations`. The source
partner-uniqueness and inverse-rescaling assumptions of the general
common-unit induction are discharged using the published actual-root
theorems. Applying that induction gives the existing
`WeylConjugationRelations` with one common unit for each simple root and
each root in both families. The low-level helper
`targetWeylRelations_powered_of_negative` retains a negative-action
premise explicitly; `targetWeylRelations_powered` discharges it.

Commutator and negative-simple cell transfer, extension over an arbitrary
affine base, and the final isogeny theorem remain separate obligations.
