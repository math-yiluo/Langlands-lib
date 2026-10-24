# Rational tensor localization of the integral finite adeles

Author: Worker 50.

The theorem `Langlands.Global.integralFiniteAdeleRationalization` proves the
published proposition `IntegralFiniteAdeleRationalization` with no parameters
or hypotheses. This is an internal derived proof for the actual integral
subring and actual finite adele ring of the rationals.

The proof views the subring inclusion as an integer-linear map and proves
that it exhibits the finite adeles as localization at the nonzero integers.
Scalar multiplication by each such integer is invertible because the finite
adeles are a rational algebra. The published lemma
`exists_integer_mul_mem_adicCompletionIntegers` in
`Langlands.Global.AdeleQuotientCompactProof` supplies a common nonzero
denominator in the ring of integers of the rationals. Mathlib's
`Rat.ringOfIntegersEquiv` transports it to an ordinary integer, and its
compatibility with the embedding in the rationals identifies its action at
every completion. Finally, equality under the subring inclusion already
implies equality, so the localization equality condition uses the denominator
one.

Mathlib's `IsLocalizedModule.isBaseChange` provides a rational-linear
equivalence from the tensor product. `AlgHom.liftEquiv` lifts the integral
subring inclusion to a rational algebra homomorphism with the same pure-tensor
formula; equality of the two linear maps proves it bijective. `AlgEquiv.ofBijective`
then supplies the desired rational algebra equivalence, whose pure-tensor
formula follows from `Algebra.smul_def`.

The tensor factors, scalar structures, subring inclusion, and finite adele
coordinates are exactly those in the published target. This proof introduces
no new global definitions or statements, no replacement arithmetic models,
and no topological assertion. Its arithmetic input is reused by its published
Lean name; the localization and base-change steps use the pinned Mathlib API
in `Mathlib.RingTheory.Localization.BaseChange`.
