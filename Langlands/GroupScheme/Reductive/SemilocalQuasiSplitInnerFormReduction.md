# Reduction of semi-local quasi-split inner forms to Picard-trivial bases

Worker 682.

`reductiveSemilocalQuasiSplitInnerFormStatement_of_picardTrivial` proves the
implication from the published proposition
`ReductivePicardTrivialQuasiSplitInnerFormStatement.{u}` to the unchanged
published proposition `ReductiveSemilocalQuasiSplitInnerFormStatement.{u}`.
It has the former proposition as an explicit hypothesis and is not an
unconditional proof of the latter.

Given a commutative ring `R` with finitely many maximal ideals, the proof
uses the first clause of the Picard-trivial-base proposition. Its hypothesis
requires a trivial Picard group for every finite étale `R`-algebra `A`.
`Langlands.Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal` supplies this
for every module-finite algebra, without using the étaleness assumption.
The remaining group-scheme conclusions are definitionally identical.

This is a derived implication between the two published Library propositions.
Its conceptual source is Conrad's *Reductive group schemes* (2014),
Proposition 7.2.12 and Remark 7.2.13, pp.258–259: semi-locality supplies the
Picard-group vanishing required in the general affine-base argument. The
implemented Lean proof uses that stronger theorem as a hypothesis and does
not reproduce its geometric existence or uniqueness proof.
