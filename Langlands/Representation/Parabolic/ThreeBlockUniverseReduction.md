# Common-universe reduction for three-block induction

Author: Worker 645.

`Langlands.Parabolic.CommonUniverseThreeBlockAssociativity.{uF,uW}` is an
internal statement for three smooth complex representations of the positive
ranks `C`, `A`, and `B`. The field lies in universe `uF`, and all three
representation carriers lie in `Type (max uF uW)`. It asserts an actual
representation equivalence between the two bracketings of canonical normalized
upper two-block induction.

The left bracketing first induces the factors of ranks `A` and `B`, then induces
that representation with the factor of rank `C`. The right bracketing first
induces the factors of ranks `C` and `A`, then induces that representation with
the factor of rank `B`. These four nodes use the literal `Shahidi.twoBlocks`
and `Shahidi.pairFamily` constructions. They use no carrier lifts. Normalized
induction stays in the common carrier universe because it takes the maximum
of that universe and `uF`.

The left action is precomposed with
`GeneralLinear.reindex (finCongr (Nat.add_assoc C A B))`. This homomorphism
runs from the group of rank `(C + A) + B` to the group of rank `C + (A + B)`,
preserving the natural row and column coordinates. Smoothness of each of the
three input representations is the only representation hypothesis.

The proved theorem `threeBlockInductionAssociativity_of_common` takes this
common-universe statement at `uW = max uV0 uV1 uV2` and yields the unchanged
Library statement
`ThreeBlockInductionAssociativityStatement.{uF,uV0,uV1,uV2}`.
It raises the three original carriers separately to
`ULift.{max uF uV0 uV1 uV2}`. The three lifted carriers therefore share a
universe, while the original carrier universes remain independent.
`isSmooth_universeLift_iff` supplies the lifted smoothness hypotheses.
Classical choice selects the equivalence asserted by the supplied common
statement, and `PadicField.heterogeneousAssociativityEquiv` transports it through
the concrete up/down factor maps.

This composition retains the original statement's four actual induction nodes,
all eight literal conjugation lifts, and the fixed rank map. It does not change
the target or any of its imports. The Lean proof binds the three lifted
smoothness proofs and the selected equivalence separately to keep reduction of
the nested action expressions manageable.

The common-universe statement is an explicit premise of the reduction theorem.
This module does not prove that premise or the closed heterogeneous theorem.
The common-universe proof still requires ordered regrouping, the two
three-block refinement geometries, singleton evaluation, and ambient rank
transport.

The provenance is internal: the statement isolates the common-universe portion
of the literal Library target, and the reduction composes the published
`Category.UniverseLift` maps with the published
`Parabolic.ThreeBlockCarrierComparison` construction. No external theorem is
claimed or translated here.
