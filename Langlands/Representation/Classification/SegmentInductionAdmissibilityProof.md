# Admissibility of actual segment tensors and induced products

`Langlands.Classification.segmentInductionAdmissibility.{uF,uV} F T`
proves the published proposition
`Langlands.Classification.SegmentInductionAdmissibilityStatement.{uF,uV} F T`.
For every prime, p-adic field `F`, supplied compatible topology `T`, positive
block rank `r`, natural length `m` and admissible smooth representation `A`
of `GL_r(F)`, it establishes admissibility of the actual increasing external
tensor, decreasing external tensor, increasing segment induction and
decreasing segment induction, in that order.

The implemented proof first applies
`isAdmissible_twist_iff` to each determinant-power twist of the admissible
input `A`. The character kernels are open by the existing determinant-power
character theorem. It applies `FiniteTensor.isAdmissible_external` to the
increasing and decreasing lists of factors, and then
`Parabolic.normalizedInductionAdmissibility` to each resulting actual
product-Levi tensor. The segment induction objects reduce to precisely those
normalized upper inductions.

The argument treats all natural lengths uniformly, including zero, and assumes
only admissibility of `A`. The field and factor-carrier universes are
independent. All four constructions use the supplied topology; both segment
inductions use the existing upper block parabolic, positive half-modulus
covariance and right translation. Reversal changes the factor order.

The provenance is internal specialization of the three existing generic
admissibility theorems, whose proofs are imported by Lean name. This module
proves admissibility only. Quotient admissibility, finite length, Jacquet
counts, adjointness, intertwiners and constituent existence remain separate
assertions.

The direct imports are the target statement and the published twist,
finite-tensor and normalized-induction admissibility proofs. The recursive
project import closure has 64 imported modules; all their Lean/Markdown pairs
were verified byte-identical to Library commit
`65f39f42712a45624ccc76ac5da7b60f52ebcd6f`. Its Classification modules
are `SegmentInductionAdmissibilityStatement`, `Segments`, `Supercuspidal`,
`SupercuspidalTwist` and `ConstituentRelations`. The other imports supply
lower-level tensor, character, parabolic, induction, topology and local-field
results. The target statement and its imported pairs are unchanged.

The closure contains no segment analytic classification, multisegment
exhaustion, ordered special-head existence, quotient coverage, tempered
uniqueness, square-integrable classification or exhaustion, or regular
exhaustion proof. No conclusion of those excluded results is used as a premise.
