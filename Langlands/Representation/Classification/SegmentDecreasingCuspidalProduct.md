# Actual decreasing cuspidal factors and ordered twist separation

Author: Worker 357.

`Langlands.Classification.segmentDecreasingCuspidalProduct` constructs
`SegmentDecreasingCuspidalProductData F T A m hr` for every supplied
`T : F.TopologicalData`, actual supercuspidal representative `A` of positive
rank `r`, and natural number of factors `m`. The field universe `uF` and
input carrier universe `uV` remain independent. The induced representation
has carrier universe `max uF uV`.

The bundle contains an actual family of supercuspidal representations on
the uniform block shape, equality of its underlying smooth objects with
`T.segmentFactorsDown A.obj m hr`, equality of its normalized induced
object with `T.segmentInducedDown A.obj m hr`, and the ordered inequality

```text
i < j  ⇒  class(A_j) ≠ class(ν A_i),     ν = |det|.
```

Classes here belong to the dependent sum over group ranks. Thus the
inequality uses exactly the rank-indexed class convention of an arbitrary
cuspidal product. It imposes only the indicated order and twist direction.
The construction also allows `m = 0`, when the ordered condition is
vacuous and both object equalities still hold.

The factors are the existing actual objects
`segmentSupercuspidalFactor F T A (m - 1 - i)`. That published constructor
uses determinant-power twisting and its proved preservation of
supercuspidality. Its smooth object is definitionally
`T.segmentFactor A.obj (m - 1 - i)`. Both bundle equalities are therefore
reflexive equalities of the actual objects; no class-level substitution,
universe enlargement of the inputs, or chosen isomorphism is used.

`segmentSupercuspidalFactorsDown_ordered_no_twist` proves the inequality.
Equality in the dependent sum first gives equality of the two
supercuspidal classes, since both ranks are `r`. Attach the same positive
rank proof to obtain an equality of actual cuspidal data. The additive
twist law identifies the right side with exponent `1 + (m - 1 - i)`.
The published `cuspidalDatum_integralTwist_injective` forces equality of
the integer exponents. The finite index bounds and `i < j` contradict
that equality by natural and integer arithmetic.

This is a derived internal construction from existing actual objects and
integral-twist freeness. Its ordered condition is intended for the
sufficient assertion of Bernstein–Zelevinsky 1977, Theorem 4.11, printed
p.456, whose proof is in section 4.15, printed pp.458–459. That source
assertion is not a premise or conclusion here. This module proves neither
nondegeneracy of a mirabolic subrepresentation nor irreducibility of a
product, and uses no derivative theorem.

The sole direct import is `SegmentTensorStabilizerProof`. An actual
recursive inventory against Library
`e3944f764d2c00d53ac87227e98601bb667f348f` found 88 inherited project
modules and 69 external import roots; every inherited Lean/Markdown pair
is byte-identical to that Library. The classification modules in this
closure are `ConstituentRelations`, `CuspidalIntegralTwistFreenessProof`
and its statement, `SegmentTensorStabilizerProof` and its statement,
`Segments`, `Supercuspidal`, `SupercuspidalSupport`, and
`SupercuspidalTwist`. No derivative module occurs.

The actual proof dependency is narrower than this import closure:
`segmentSupercuspidalFactor` uses actual supercuspidal twisting, and
`cuspidalDatum_integralTwist_injective` applies integral-twist freeness
after an inverse twist. Freeness uses the published admissible Schur
central character and evaluation of a scalar uniformizer as
`q^(-r*s)`, with `q > 1` and `r > 0`, to force the twisting exponent to
vanish. It does not use a segment constituent or a classification theorem.
The remaining stabilizer and cuspidal-tensor branches of the imported
module are not invoked in this construction; their imports supply
finite Weyl combinatorics, tensor and coinvariant definitions, admissible
tensor arguments and actual smooth transfer.

In particular, no individual head or socle existence, segment derivative
or Jacquet formula, special-head or socle product criterion, generic
segment-product uniqueness, ordered multisegment existence, exhaustion,
coverage, ordered conversion, tempered uniqueness, square-integrable
classification or exhaustion, or regular exhaustion occurs in the
import closure or implemented proof. The existing full
`SegmentHeadProductIrreducibility` obligation remains open.
