# Distinct members and inducing tensors of a segment

Author: Worker 495.

This proof supplies
`Langlands.Classification.segmentTensorStabilizerAndCuspidality.{uF,uV} F T`
of the grouped proposition
`Langlands.Classification.SegmentTensorStabilizerAndCuspidality.{uF,uV} F T`.
Its outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)` and has no additional theorem-valued premise.
It derives the actual tensor properties from integral-twist freeness,
the generic distinct-factor stabilizer theorem and the cuspidal tensor
theorem. It does not construct a segment constituent.

The field and representation-carrier universes remain independent.
`cuspidalDatum_integralTwist_injective` applies the inverse of the second
twist to an equality of two integral twists. The additive twist law
gives a twist by their difference fixing the original datum. The
integral-freeness theorem forces this difference to be zero.
`segment_member_injective` restricts this result to natural indices.
It asserts injectivity on all natural indices, and hence on the finite
range defining an actual segment.

`segmentSupercuspidalFactor` is the actual supercuspidal object obtained
by the existing determinant-character twist. The published twist theorem
supplies its supercuspidal property, and
`segmentSupercuspidalFactor_obj` checks that its smooth object is
definitionally the existing `T.segmentFactor`.

For any positive rank and any injective integral index function on
`Fin m`, `segmentSupercuspidalFactor_datum_injective` identifies the
cuspidal datum of each factor with the corresponding actual twist of the
base datum. Integral injectivity then proves these data distinct.
`segmentTensorStabilizer_count` applies the generic count to the actual
uniform block shape and these actual supercuspidal factors. It includes
`m = 0`; no existence of segment constituents is asserted.

The exact wrappers `segmentFactors_tensorStabilizer_count` and
`segmentFactorsDown_tensorStabilizer_count` state the formula for the
existing `T.segmentFactors` and `T.segmentFactorsDown` smooth objects.
The natural-index adapter first applies integral-twist injectivity to
the integer casts of two equal natural twists. The increasing case then
uses injectivity of the finite index coordinate. For the decreasing case,
`omega` proves injectivity of `m - 1 - i` from the finite bounds. Both
wrappers apply the generic stabilizer theorem directly to the actual
supercuspidal factors, including the vacuous case `m = 0`.

The two helpers `segmentFactors_isIrreducible_isLeviCuspidal` and
`segmentFactorsDown_isIrreducible_isLeviCuspidal` provide the actual smooth
tensor objects needed by an associated-induction map theorem. They require
positive `m`, so `Nat.mul_pos` supplies the positive total rank required by
the published `CuspidalSupport.glCuspidalTensor`. Apply that theorem to the
actual determinant twists of `A` in the increasing and decreasing orders.
Their underlying smooth objects are definitionally the existing segment
factors, so no transport or class-level substitution is used. Each
conclusion includes both irreducibility and admissible quasicuspidality
on the actual product Levi. The latter tests zero coinvariants for every
proper standard refinement, as in the existing `IsLeviCuspidal` definition.
These two helpers use no twist-freeness or distinctness argument; the
published cuspidal-tensor proof uses scalar endomorphisms, admissible
external tensors and the vanishing of one proper block's coinvariants.

The exact wrapper installs the supplied topology and applies the two
actual count lemmas for every factor count. Given positive length, it
applies the two actual irreducibility/cuspidality lemmas. All objects in
this assembly are definitionally the ones in the aggregate statement;
no replacement of actual objects by their classes is used.

These are internal lower-level adapters. A recursive audit of all 86
project modules in the import closure, including this module, found no
missing modules or unpaired Lean files. Besides the present proof and its
statement, the classification modules are precisely `ConstituentRelations`,
`CuspidalIntegralTwistFreenessProof`, its statement, `Segments`,
`Supercuspidal`, `SupercuspidalSupport` and `SupercuspidalTwist`.
The freeness branch uses only determinant-character algebra and local-field
normalization. The generic stabilizer branch extracts the actual factor
equivalences, fixes their block correspondence and applies minimal Weyl
double-coset uniqueness. The cuspidal tensor branch uses scalar
endomorphisms, admissible external tensors and proper-refinement
coinvariant vanishing. The remaining branches provide smooth transfer,
finite tensors, twists, coinvariant definitions and finite Weyl
combinatorics.

In particular, the imported `JacquetInductionStatement` is an interface
definition; no Jacquet-filtration theorem or multiplicity formula is
invoked. The implemented proof uses no individual segment head/socle
existence, segment analytic classification, generic segment-product
uniqueness, special-head product irreducibility, ordered head/socle
existence, multisegment exhaustion, coverage or conversion, tempered
uniqueness, square-integrable classification or exhaustion, or regular
exhaustion. This applies to direct and transitive proof dependencies.
The proof constructs no induced strong head or socle.
