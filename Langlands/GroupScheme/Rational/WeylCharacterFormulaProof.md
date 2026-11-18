# The Weyl character formula for a split reductive group in characteristic zero

Module `Langlands.GroupScheme.Rational.WeylCharacterFormulaProof`.

## Main theorem

`Langlands.GroupScheme.weylCharacterFormulaStatement :
WeylCharacterFormulaStatement.{u}` proves the published proposition
`Langlands.GroupScheme.WeylCharacterFormulaStatement` (module
`Langlands.GroupScheme.Rational.WeylCharacterFormulaStatement`) for every universe
`u`, with no further hypotheses. That proposition is the Weyl character formula
(Milne, *Algebraic Groups* (2017), Theorem 22.52, in characteristic zero) for a
split pinning `p` of a group scheme `G` over a field `k` of characteristic zero.
Let `rho` be a character with `2 • rho` equal to the sum of the positive roots,
and write `J μ = ∑_{w ∈ W} det(w) e^{w μ}` in `ℤ[X]`. Then every representation
`r` with `p.IsHighestWeight r lam` has character `c`, with
`c μ = dim r_μ`, satisfying `J(rho) · c = J(lam + rho)`.

## Proof

The proof is the single term

`weylCharacterFormulaStatement_of_freudenthal freudenthalMultiplicityStatement`.

It combines two results, each proved in its own module.

1. `Langlands.GroupScheme.freudenthalMultiplicityStatement` (module
   `Langlands.GroupScheme.Rational.FreudenthalMultiplicityProof`) proves
   Freudenthal's multiplicity formula `FreudenthalMultiplicityStatement` (module
   `Langlands.GroupScheme.Rational.FreudenthalMultiplicityStatement`; Humphreys,
   *Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.3). For
   each highest-weight representation it gives a symmetric, Weyl-invariant,
   positive definite rational form `F` on the character lattice, together with
   the recursion for weight multiplicities. The proof is a trace computation
   with a Casimir element. The element is built from the trace form of the pair
   Lie algebra of a closed linear embedding of `G` and of `r`. See that module's
   Markdown, and `Langlands.LinearAlgebra.FreudenthalCasimirCore` for the
   abstract recursion.
2. `Langlands.GroupScheme.weylCharacterFormulaStatement_of_freudenthal` (module
   `Langlands.GroupScheme.Rational.WeylCharacterFormula`) derives the Weyl
   character formula from Freudenthal's formula without further representation
   theory. The witness is `c = p.weightMultiplicity r`, the finitely supported
   function of weight multiplicities. The identity `J(rho) · c = J(lam + rho)` is
   `LinearAlgebra.WeylCharacter.alternant_mul_ofCoeff_eq` (module
   `Langlands.LinearAlgebra.FreudenthalWeylCharacter`). That theorem is a purely
   combinatorial statement about root data. Its inputs are the Weyl invariance of
   `c`, the value `c(lam) = 1`, the support of `c` lying below `lam`, and
   Freudenthal's recursion for `c`. Its proof uses the Weyl denominator identity
   (`Langlands.LinearAlgebra.WeylDenominatorIdentity`), a Laplacian-type operator
   on `ℤ[X]`, and the fact that strictly dominant weights have trivial stabilizer
   in the reflection group (`Langlands.LinearAlgebra.SimpleReflectionWords`).

## Route

This route differs from Milne's, which uses the cohomology of line bundles on
`G/B` (Theorems 22.48, 22.50 and 22.51). It is the algebraic route suggested in the
statement's Markdown (section "For the later proof"): characteristic zero enters
only through the Casimir operator and Freudenthal's formula.
