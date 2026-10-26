# Analytic inverse-transpose transport

Author: Worker 363.

The closed theorem is
`Langlands.Classification.padicInverseTransposeAnalytic :
PadicInverseTransposeAnalyticStatement.{uF,uV}`. The field and representation
carrier universes remain independent, and the target retains every prime,
compatible topological realization, positive rank, and complex representation.

The generic helper proofs take topological groups G and H, with Borel
measurable structures on their central quotients, a continuous group equivalence
`e : H ≃ₜ* G`, and a Haar measure `μ` on the actual central quotient of H. The published
`centralQuotientCongr e` maps that quotient to the actual central quotient of G.
Mathlib's `ContinuousMulEquiv.isHaarMeasure_map` makes its pushforward of μ a
Haar measure. The existing analytic predicate for ρ is applied to this measure.
It supplies admissibility and a unitary central character for that measure.

Admissibility is transported using the published
`isAdmissible_comp_continuousMulEquiv`, whose proof handles every open subgroup
through inverse comap and equality of fixed-vector spaces. This respects the
Library's all-open-subgroup definition. The character is transported by
`UnitaryCentralCharacter.compContinuousMulEquiv` from
`Langlands.Representation.MatrixCoefficient.GroupTransport`.
For each smooth functional of the pullback,
`isSmoothVector_dual_comp_continuousMulEquiv_iff` places the same underlying
algebraic functional in the original smooth dual.
`UnitaryCentralCharacter.coefficientNorm_compContinuousMulEquiv` rewrites the
descended norm as the original norm composed with the quotient map. The
quotient map is measurable by its continuity and the Borel structures.
Mathlib's `MemLp.comp_of_map` then gives the needed bound for μ.
The argument applies at exponent 2 and separately at every exponent 2 + ε,
with ε positive, retaining the central-character witness under each measure.

The p-adic helpers quantify over every Borel Haar measure and apply these generic
lemmas. The final theorem specializes to `T.generalLinearInverseTranspose n`.
For reflection it applies the same preservation statement a second time and
uses `GeneralLinear.inverseTranspose_involutive` to prove equality of the twice
pulled-back representation and the original representation.

This is an internally derived change-of-variables proof from existing analytic
and representation definitions; no external literature is used. The actual
central quotient map, central character and coefficient identity are imported
from `MatrixCoefficient.GroupTransport`; all-open admissibility comes from
`CuspidalSupport.GroupTransport`, and smooth-dual transport comes from
`CompactCoefficient.GroupTransport`. The new proofs assemble these constructions
with Mathlib's Haar pushforward and measurable composition lemmas.
The argument assumes no exact invariance of an arbitrary
Haar measure, no classification or exhaustion result, and no identification
with the smooth contragredient. The construction prerequisite supplies actual
maps and their laws; the final target has no extra transport-data hypothesis.
