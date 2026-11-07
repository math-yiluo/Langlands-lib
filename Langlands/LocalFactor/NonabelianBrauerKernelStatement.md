# Arithmetic compatibility of actual abelian epsilon ratios

`KernelCompatibility F e` states the missing arithmetic identity for the actual
Brauer presentation of the continuous exact dimension-zero group. For a
normalized supplied reciprocity family, every intermediate field `E`, every
nontrivial unitary additive character on `E`, every family of actual regular
additive Haar measures, and every finite integer combination `z` of nested
field-character differences, it asserts the following implication: if the
actual induced virtual class is zero, the product of the actual abelian epsilon
ratios, raised to their integer multiplicities, is one.

The Lean equality `evaluationMap ... z = 0` uses `Additive ℂˣ`, where zero is the
complex unit one. The equality `presentationMap ... z = 0` is in the subtype
`DegreeZero F E` of the original continuous exact Grothendieck group. The map
uses actual induction, and the evaluation uses the actual trace additive
character and the unchanged integral epsilon expression. Haar-family
independence is already proved in the presentation module. No decomposition,
assignment, descent map, or compatibility hypothesis is supplied as an input
other than the existing normalized reciprocity premise. Both the field universe
and independent representation universe occur in the complete telescope.

`KernelCompatibilityStatement` universally quantifies over primes, finite
p-adic fields and supplied reciprocity families. Both declarations return
`Prop`. This module proves neither of them and constructs no nonabelian system.

The source is Pierre Deligne, *Les constantes des equations fonctionnelles des
fonctions L* (1973), theorem 4.1 and §4.2, §4.7–4.11. Registered literature ID:
`deligne-1973-local-constants`; source SHA256:
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
The original PDF pages 36 and 40 (printed 536 and 540) were rendered and checked.
Section 4.2, formula (4.2.1), evaluates degree-zero monomial sums by products of
abelian constants. Lemma 4.7 on printed page 540 says the product is one on the
kernel of the induction presentation for a finite Galois extension and a fixed
quasicharacter twist; its formula (4.7.1) then descends those values. Sections
4.9–4.11 pass from finite Galois representations to continuous Weil
representations in the proof of theorem 4.1.

This statement is a derived common-closure counterpart, not a literal restatement
of the finite-group lemma. The generators here include arbitrary pairs of
characters on every finite intermediate field in one fixed closure. The usual
character-minus-trivial generators give such pairs by subtraction. The
published generation theorem covers the actual continuous exact quotient.
The arithmetic assertion is required independently of generation; no proof of
it follows merely from surjectivity. The source theorem gives the mathematical
provenance of the assertion, while its unconditional formal proof remains a
separate obligation. The supported specialization is finite extensions of
`Q_p` and complex coefficients; no comparison of different closures is claimed.
