# Actual unequal-rank zeta values at the inverse character

Worker 318's internal proposition
`InducedTailIntermediateInverseCharacterStatement.{uF,uV,uW}` states equality
of the actual unequal-rank rational zeta-value sets at `ψ` and
`ψ.scale (-1)`. The latter character is the pointwise inverse of `ψ`.
The bundled `UnitaryAdditiveCharacter` is continuous, unitary and nontrivial.

The quantifiers retain every prime, every p-adic field in universe `uF`, every
supplied topological realization `T`, and natural indices `n,r,j,k` with
`r = n + (j + k + 1)`. The two representations act on independent complex
module universes `uV` and `uW`, at matrix ranks `r+1` and `n+1`. They are
arbitrary representations; no Whittaker-type, smoothness or irreducibility
hypothesis is added. The published value sets themselves require actual
coefficient-image membership, a half-plane of absolute convergence, and
rational continuation of the corresponding integrals. Equality transports
these witnesses and does not assert that nonzero values exist.

The scalar measure is any supplied additive Haar measure. Both sides use its
actual rectangular product on `j` by `n+1` matrices, without renormalization.
The original and inverse-character quotient measures may be supplied
independently. Each must satisfy the full published `IsCompatible` predicate
for the same normalized `generalLinearHaar` and `unipotentHaar` inputs.
The conclusion compares `unequalRankZetaValuesAt` with the same rank equation,
representations, residue cardinality and normalized absolute value, changing
only the additive character and the independently supplied quotient measure.
The Borel structures are those of the supplied topology. Empty rectangular
row indices are allowed. There is no residual scalar or Laurent multiplier.

This is a derived internal interface for the intermediate-tail comparison,
using published character-change and quotient-measure constructions. The
unit `-1` has absolute value one, so the determinant factor and the quotient
and rectangular measure moduli are one. Exact uniqueness for the fixed Haar
inputs identifies each compatible quotient measure with the canonical one.
These facts motivate a separate proof using the published forward and reverse
actual-value transports. This file states the proposition only. It neither
asserts quotient disintegration or representation extension nor proves the
closed intermediate-tail Laurent-span inclusion.
