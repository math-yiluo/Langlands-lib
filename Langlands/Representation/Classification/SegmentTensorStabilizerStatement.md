# Stabilizer counts and cuspidality of actual segment tensors

Author: Worker 495.

`Langlands.Classification.SegmentTensorStabilizerAndCuspidality.{uF,uV} F T`
is an internal proposition grouping the finite tensor premises used for
individual segment constituent existence. Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The supplied compatible topology is installed, and the field universe
`uF` and representation-carrier universe `uV` remain independent.

For every positive block rank `r`, every natural factor count `m`, and
every actual supercuspidal representative `A` of `GL_r(F)`, set
`B = BlockShape.uniform m r hr`. The proposition uses the actual smooth
external tensor objects

- `σ = FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)`,
  with determinant powers `0, 1, …, m - 1`;
- `τ = FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj m hr)`,
  with the same powers in decreasing order.

It asserts that both actual self-associating minimal coordinate-permutation
sets, `AssociatingPermutations B B σ.representation σ.representation` and
the corresponding set for `τ`, have natural cardinality one. These are
permutations of the actual coordinates with actual inverse-Levi-conjugation
representation equivalences, subject to the existing minimality condition.
They are not multisets of classes or sets of all conjugating permutations.
Both count assertions include `m = 0` and its empty tensor.

For `0 < m`, it also asserts that each of `σ` and `τ` is irreducible
and satisfies the existing `CuspidalSupport.IsLeviCuspidal B` predicate.
That predicate requires admissibility of the actual Levi representation
and zero ordinary coinvariants under the unipotent radicals of all
proper standard refinements of `B`. The proposition does not request
these two properties at `m = 0`. It makes no assertion about the
irreducibility of a parabolically induced representation.

The provenance is internal. This interface isolates a small group of
actual tensor premises in the segment-existence construction. Its only
constructions are the published determinant-power factor families,
external smooth tensor object, association set and Levi cuspidality.
A prospective proof can combine integral-twist freeness with the generic
distinct-factor stabilizer count, and apply the cuspidal external-tensor
theorem to the actual factors. Those theorems are not assumptions of
this proposition; the proof remains a separate obligation. No external
literature theorem is translated here.

The imports contain no individual segment head/socle existence, segment
analytic classification, generic segment-product uniqueness, special-head
product irreducibility, ordered head/socle existence, multisegment
exhaustion, coverage or conversion, tempered uniqueness, square-integrable
classification or exhaustion, or regular exhaustion. The statement has
no Jacquet-filtration, induced-map or classification premise and proves
no segment constituent existence.

This file defines the proposition only. The stabilizer counts and
positive-length tensor properties require independent proof and review.
