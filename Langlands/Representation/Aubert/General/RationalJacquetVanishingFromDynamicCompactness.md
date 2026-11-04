# Rational Jacquet vanishing from two uniform prerequisites

This internal assembly retains exactly two uniform mathematical prerequisites:
`BruhatTits.DynamicParabolicQuotientCompactStatement.{u}` and
`RationalCuspidalSupportAssociationStatement.{u,v}`.
Neither prerequisite is proved here. The conditional theorem concludes the whole
unapplied `RationalSupportCategoryJacquetVanishingStatement.{u,v}`.
It is supporting work for that exact proof obligation, which remains open
until both prerequisites have been discharged.

## Certified witness

`dynamicAssociatedSubsetOfNonzeroJacquet` takes the actual rational-point
families, their structural and topology hypotheses, a smooth support-category
object `E`, and a nontrivial actual normalized Jacquet module at `K`.
It returns a pair `(J,n)` together with `J ⊆ K`, the actual certificate
`rootAssociation i ν hN hZ I J n`, and
`x ∈ M_J ↔ n⁻¹ * x * n ∈ M_I` for every actual rational point `x`.
Both certificates use the same point `n`.

The construction applies
[`rationalAssociatedSubsetOfNonzeroJacquet`](RationalJacquetSupportVanishingReduction.md).
It supplies ambient quotient compactness with
`Langlands.Aubert.General.compactSpace_leftQuotient_parabolic` from
[RationalInductionDualityReduction](RationalInductionDualityReduction.md),
using the uniform dynamic compactness premise and the target's
`StandardCocharacterStatement`.
It supplies compactness of each literal subgroup-of-Levi quotient with
`compactSpace_leftQuotient_in_levi_of_dynamic` from
[RationalLeviQuotientCompactness](RationalLeviQuotientCompactness.md).
The latter retains the actual quotient topology and uses the target's
Levi-intersection data. Finally, the construction specializes the uniform
rational association premise to this field, group, torus, cocharacter and the
displayed standard, root, normalizer, centralizer and closedness data.
Thus there is no additional family-level compactness or association premise.

## Whole-target conditional corollary

`rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`
introduces every binder of the published rational vanishing proposition.
Connected reductivity supplies its affine instance, and the maximal split
torus hypothesis supplies its monomorphism instance. The proof installs exactly
the canonical evaluation topology `pointTopology` and the target's finite
simple-root instance. If the actual Jacquet module of `E` were not a
subsingleton, it would be nontrivial. The certified witness above then
contradicts the literal target hypothesis `hno J n hJK hIJ hn`.

The field universe `u` and carrier parameter `v` remain independent, with
complex representation carriers in `max (u + 1) v`. The conclusion covers
every smooth object in the actual support category. There are no
finite-length, admissibility, characteristic-zero, split-group, quasisplit-group,
nonempty-root or positive-rank restrictions. Neither a cardinality inequality
nor a Grothendieck-group equality replaces the target's quantified negation
or the actual Jacquet module.

## Dependencies and provenance

This is derived internal content assembled by Worker 158 with Worker 593's
compactness adapter and agreed whole-target interface. It introduces no new
direct literature assertion. The imported target and its dependency pairs
are preserved.

The representation-theoretic route is the published
[RationalJacquetSupportVanishingReduction](RationalJacquetSupportVanishingReduction.md):
inside-Levi cuspidal embedding, actual exact normalized induction and induction
in stages, the common-constituent construction, actual cuspidality transport,
and composition of actual root-association representatives.
The common-constituent construction and cuspidal embedding transitively use
`Langlands.Aubert.General.FirstAdjointness.equiv` for the actual normalized
functors on locally compact nonarchimedean groups, under semidirect-decomposition,
closed-radical and `IsUnimodularModulus` hypotheses. Its group, source-carrier
and target-carrier universes are independent; it requires neither finite length
nor quotient compactness. Their separate finite-generation steps use
`Langlands.Aubert.General.JacquetFiniteGeneration.finite_of_compactQuotient` under the
corresponding quotient compactness hypothesis, now supplied conditionally by
the displayed dynamic premise. The rational adapter discharges the standard
unipotent unimodularity hypotheses.

This module applies no classification, character-independence or geometric-lemma
result to prove the uniform association premise. That premise is retained in
full, including its actual conjugation and inducing-data isomorphism
certificates; its eventual proof must supply its own dependency ledger.
