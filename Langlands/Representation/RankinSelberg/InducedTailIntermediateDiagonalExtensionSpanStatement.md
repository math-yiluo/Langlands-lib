# Conditional intermediate-tail span from diagonal extension and disintegration

Worker 318 isolates one conditional step of the intermediate-test-rank
calculation. `InducedTailIntermediateDiagonalExtensionSpanStatement` is a
closed proposition with independent field, full-representation and
test-representation universes. It is internal infrastructure for the existing
`InducedTailIntermediateRankSpanStatement`, whose four-universe canonical
induced representation and same-character conclusion remain unchanged.

Write `a=n+1`, `d=k+1`, and `c=c0+1`. The full representation has rank
`a+d+c`; the test representation has rank `a+d`; and the given tail function
has rank `a`. All ranks are positive where the coefficient APIs require them.
The canonical p-adic topology, normalized absolute value and residue
cardinality are used throughout. The coefficient functions use a supplied
continuous, nontrivial unitary additive character `psi`; continuity and
nontriviality are bundled in `UnitaryAdditiveCharacter`.

The proposition retains these mathematical premises:

- The full representation is of Whittaker type for the standard character
  at `psi`. The test representation is smooth, and the test function belongs
  to its actual inverse coefficient image at `psi`.
- For every Schwartz function `Phi` on the last row of `GL_a`, an actual
  coefficient of the full representation restricts on
  `lowerBlockLocalization c g 0 1` to the tail function times
  `Phi (lastRow g)` times `|det g|^((d+c)/2)`. The tail function is a standard
  Whittaker function; membership in a particular representation's coefficient
  image is not needed for this step.
- The supplied small and full quotient measures and parameter measures
  satisfy the stated transfer formula for every Borel measurable complex
  function. The parameter measures are s-finite, positive on nonempty open
  sets and finite on compact sets; the small quotient measure is s-finite.
  The real normalization constant `C` is strictly positive.

The chart in that premise is the published actual
`lowerBlockQuotientChart`, followed by
`upperUnipotentQuotientCongr` for the numerical equality
`(n+1)+d=(n+d)+1`. Its representative is the actual lower-block matrix
`[[g,0],[x,h]]`, with `x` having `d` rows and `a` columns and `h` in the
lower-triangular subgroup of rank `d`. The small quotient density is literally
`ofReal (quotientDeterminantAbs abv n q ^ (-(d : Z)))`. Both expressions are
local bindings of the existing constructions, so this statement requires
only published imports. The transfer premise includes both directions of
absolute integrability and the integral formula with scalar `(C : Complex)`.
It does not assert that arbitrary measures satisfy these formulas.

The tail quotient integrand uses the original inverse test function as a
standard function at `psi.scale (-1)` and the original standard tail function
as an inverse function at that scaled character. The published same-function
recasts perform these conversions. A numerical equality transports the test
index to the zero-row tail rank gap `k+1`; the functions themselves are not
changed. If these quotient integrands are integrable on a right half-plane
and their quotient integrals have rational continuation `R`, the conclusion
places `R` in the actual full zero-row Laurent span. The full side uses
`psi`, the supplied full quotient measure, the point mass at the unique
zero-row matrix, and the full representation transported only along its
displayed numerical rank equality.

Provenance is internal: the proposition records the interface obtained by
composing the published coefficient recasts, actual lower-block coordinates,
zero-row cutoff, Whittaker localization and actual zeta-value definitions.
It is motivated by the intermediate-rank case of JPSS section 9.3, but it
does not attribute a new theorem or a verbatim statement to that source.
This file states a conditional implication. It supplies no proof of diagonal
extension, full Whittaker type, quotient disintegration, character or measure
transport to the canonical same-character tail, or the unchanged closed
intermediate-rank span theorem.
