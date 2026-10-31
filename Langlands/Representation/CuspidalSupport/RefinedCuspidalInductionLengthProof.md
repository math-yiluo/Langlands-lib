# Admissibility and finite length of actual refined cuspidal induction

Authors: Worker 636 and Worker 717.

`Langlands.CuspidalSupport.refinedCuspidalInductionFiniteLength.{uF,uV}`
proves the exact published proposition
[`RefinedCuspidalInductionFiniteLengthStatement`](RefinedCuspidalInductionLengthStatement.md).
The field universe `uF` and inducing-carrier universe `uV` are independent.
Every prime, actual finite p-adic extension, compatible topology and natural
rank is included, including rank zero.

For an arbitrary irreducible Levi-cuspidal representation `ω` of the
flattened fine Levi, put
`σ = ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom` and
`I = Rep.of (T.normalizedRefinedInduced B S σ)`.
The theorem gives all three conclusions for this same `I`: admissibility,
finite length of its module over the complex group algebra of
`B.Levi F.Carrier`, and some `m : ℕ` with
`HasCompositionSeriesLength I m`. This last assertion supplies an actual
invariant-subspace composition series with actual irreducible quotient
representations. The induced carrier is in universe `max uF uV`, with the
existing right-translation action and positive half-modulus covariance.

The Lean proof applies the published
`refinedCuspidalInductionReductionClause_holds.{uF,uV}` from
[`RefinedCuspidalInductionReduction`](RefinedCuspidalInductionReduction.md).
Its premise asks for standard cuspidal induction length in every positive
rank. The lambda supplies the unconditional published theorem
`cuspidalInductionLength.{uF,uV} F T n` from
[`NormalizedCuspidalInductionLengthProof`](NormalizedCuspidalInductionLengthProof.md)
for each prime, field, topology and rank. That theorem holds in all natural
ranks, so the lambda needs no use of the positivity argument. Thus the
reduction's premise is discharged by a proved theorem.

The imported reduction contains the mathematical argument. In positive rank,
induction in stages and the flattened-Levi comparison identify the outer
normalized induction of `I` with standard cuspidal induction of `ω`, giving
finite length for that outer induction. Admissibility of `I` gives
admissibility of the outer induction. Its finite length implies finite
generation, so its normalized Jacquet module has finite length. Compact local
sections make evaluation from that Jacquet module onto `I` surjective.
Finite length passes to this quotient, and the published composition-series
bridge produces the actual series. The reduction treats rank zero with
`refinedCuspidalInductionFiniteLength_rankZero`.

The provenance is internal: this module discharges the premise of an existing
published reduction using the existing standard cuspidal-induction theorem.
The linked proof explanations record the provenance and implementation of
those ingredients. Worker 717 supplied the reduction and the assembly
template; Worker 636 verified the published input, supplied its actual theorem
and import, and completed this proof pair. The target statement and its
imports are preserved. No tensor presentation, supplied series, finiteness or
dimension premise, rank restriction, or extra theorem-valued premise is added.
