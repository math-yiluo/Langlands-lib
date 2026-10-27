# Admissibility of segment tensors and induced products

`Langlands.Classification.SegmentInductionAdmissibilityStatement.{uF,uV} F T`
is an internal proposition about the existing actual segment constructions.
For every prime, p-adic field `F`, supplied compatible topology `T`, positive
block rank `r`, natural length `m`, and smooth representation `A` of
`GL_r(F)` with carrier universe `uV`, it asserts that admissibility of `A`
implies admissibility of four representations, in this order:

1. The external tensor of the increasing factors
   `(A, νA, ..., ν^(m-1) A)`.
2. The external tensor of the decreasing factors
   `(ν^(m-1) A, ..., νA, A)`.
3. The representation of `T.segmentInduced A m hr`.
4. The representation of `T.segmentInducedDown A m hr`.

The tensor representations act on the existing `PiTensorProduct` carriers
for the product Levi of `BlockShape.uniform m r hr`. The induced carriers
have universe `max uF uV`, as in the segment definitions. The field and
factor-carrier universes are independent. The proposition includes `m = 0`,
and it does not require irreducibility or supercuspidality of `A`.
Admissibility means smoothness and finite-dimensional fixed vectors for
every open subgroup, using the supplied topology.

The induced representations are the actual smooth normalized inductions
from the standard upper block parabolic, with positive half-modulus
covariance and right translation. Reversing the factors changes their
order; it does not change the parabolic or the normalization.

The provenance is internal specialization of existing results. Open-kernel
character twists preserve admissibility
(`Langlands.isAdmissible_twist_iff`); the determinant-power characters used
by the segment factors have open kernels. Finite external tensors of
admissible factors are admissible
(`Langlands.FiniteTensor.isAdmissible_external`), and actual normalized
parabolic induction preserves admissibility
(`Langlands.Parabolic.normalizedInductionAdmissibility`). These explain the
intended derivation; this module contains the proposition alone.

Its sole project import is `Classification.Segments`, which supplies the
actual factors, tensor construction and induced objects. No classification
conclusion is assumed. The proposition supplies no proof, quotient
admissibility theorem, finite-length assertion, Jacquet count, adjointness,
intertwiner, irreducibility or segment constituent.

The recursive project import closure contains 47 imported modules.
Their Lean/Markdown pairs were verified byte-identical to Library commit
`5d39e7f75dfe6dd6673ea118c8f50ea30169f516`. Its Classification modules are
`Segments`, `Supercuspidal`, `SupercuspidalTwist` and
`ConstituentRelations`; these provide definitions and lower compatibility
results. No excluded segment analytic, multisegment, tempered,
square-integrable or regular classification proof is in that closure.
