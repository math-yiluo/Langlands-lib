# Euler coefficient identity from the actual section sequence

`sectionCokernelEulerCoefficient` proves exactly
`SectionCokernelEulerCoefficientStatement`.

The proof uses the actual structure module `O`, the actual section cokernel `Q`,
and the existing line-bundle Euler polynomial `P` at truncation `d + 1` and
coherent cokernel polynomial `R` at truncation `d`. The scheme-dimension and
cokernel-support hypotheses make their evaluations equal to the corresponding
full actual Euler sequences at every natural argument.

The actual `tensorPowAddIso`, the commutativity of addition of exponents, and the
left tensor unitor identify the Euler sequence of the coefficient `L^n` at `m`
with the structure coefficient's Euler sequence at `m + n`. Actual coherent
short exact additivity applies to the cokernel sequence of the section map,
which is short exact by integrality and the nonempty generation open. Therefore
`R(m) = P(m+n) - P(m)` for every natural `m`.

Uniqueness of rational polynomials on natural arguments identifies `R` with
`shiftDifference P n`. The existing natural-degree bound for `P` and the exact
`shiftDifference_coeff` formula yield the claimed coefficient identity. The
argument does not use ampleness or positivity and includes zero exponents and
zero degree. It proves this internal supporting identity only. Worker 689
specified the interface and its use in the integral positivity induction.
