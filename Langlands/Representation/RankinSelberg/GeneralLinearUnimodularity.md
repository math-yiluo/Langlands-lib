# Right invariance of the normalized general linear Haar measure

Worker 116 proves
`Langlands.RankinSelberg.generalLinearHaarRightInvariant`, whose conclusion is
exactly the published
`Langlands.RankinSelberg.GeneralLinearHaarRightInvariantStatement F n`.
The companion instance `generalLinearHaar_isMulRightInvariant` exposes
`MeasureTheory.Measure.IsMulRightInvariant (generalLinearHaar F n)` to
instance search.

The theorem takes an arbitrary `F : Type uF` with `Field F`, `ValuativeRel F`,
`TopologicalSpace F`, and `IsNonarchimedeanLocalField F`, every natural `n`,
and measurable and Borel structures only on
`Matrix.GeneralLinearGroup (Fin (n + 1)) F`. It adds no field-characteristic,
countability, unimodularity, or quotient-existence hypothesis. In particular,
`n = 0` is included. The concluding unapplied-constant example checks the
whole parameter telescope in the same order as the published statement.

## Implemented algebraic argument

The private namespace `GeneralLinearUnimodularity` works over an arbitrary
field and an arbitrary finite index type. It constructs diagonal matrix units
from functions into the field's units and permutation matrix units. For any
monoid homomorphism `χ : GL →* ℝ≥0`, intertwining two group elements by an
invertible matrix makes their character values equal. Cancellation is valid
because a group element maps to a unit, hence to a nonzero nonnegative real.

Assume this character takes value one on scalar matrices. Permutation
conjugation gives the same character value to each one-coordinate diagonal
matrix with a fixed unit entry `a`. The product over all coordinates is the
scalar matrix `a`. Thus the common nonnegative value has its positive
`Fintype.card`-th power equal to one, so it is one. The index used in this
argument supplies nonemptiness. Every diagonal unit is a product of its
one-coordinate factors, so its value is one; this also handles an empty
index type without invoking the nonempty argument.

For a transvection `I + c E_ij`, with `i ≠ j`, take the diagonal unit with
entry `-1` at `i` and entry `1` elsewhere. It intertwines the transvection
with `I - c E_ij`, its inverse. Their character values are therefore equal,
and their product has value one. The square of the nonnegative character
value is one, so the value is one. This argument applies in characteristic
two as well, where the transvection equals its inverse.

Finally, pinned Mathlib's
`Matrix.diagonal_transvection_induction_of_det_ne_zero` reduces an arbitrary
invertible matrix to invertible diagonals, transvections, and products. The
induction predicate quantifies over all matrix units having the given
underlying matrix. This transfers the matrix induction directly to `GL`
without assuming an additional generation result. These steps prove the
private `character_eq_one` helper.

## Application to the project measure

The local-field hypotheses imply Hausdorffness through the additive uniform
structure. Finite matrix spaces are locally compact, and the matrix-unit
topology consequently supplies a locally compact topological group.
Mathlib's `MeasureTheory.Measure.modularCharacter` is then available without
assuming its continuity.

A scalar matrix commutes with every matrix unit, so its right translation
is the same function as its left translation. Left invariance of
`generalLinearHaar F n` implies that mapping this measure by that right
translation leaves it unchanged. The identity
`modularCharacterFun_eq_haarScalarFactor`, followed by
`haarScalarFactor_self`, therefore gives modular-character value one on
scalars. The algebraic argument proves that the modular character is one on
every group element.

For any right translation, the mapped measure is left invariant and regular;
regularity is transported along `Homeomorph.mulRight`. The theorem
`isMulLeftInvariant_eq_smul_of_regular` identifies this mapped measure with
the original measure scaled by its Haar scalar factor. That factor equals
the modular character, hence is one. This proves the required right
invariance. Using regular Haar uniqueness avoids requiring full inner
regularity or introducing a countability hypothesis.

## Provenance and normalization

This is an internal derived proof of the already published project statement,
not a transcription of a theorem or proof from external literature. Its
algebraic helpers are proved in this module. The imported mathematical inputs
are the published `UnimodularityStatement` and its `Measures` dependency, and
Mathlib at pinned commit `5ed2965256430c3649e86755f9576b54eca72435`, particularly
`LinearAlgebra/Matrix/Transvection.lean`,
`MeasureTheory/Group/ModularCharacter.lean`, and
`MeasureTheory/Measure/Haar/Unique.lean`.

The proof applies to the existing `generalLinearHaar F n` throughout. That
measure retains its published normalization assigning mass one to the
integral general-linear subgroup. No measure or statement dependency is
modified, and no quotient measure is constructed or assumed. The result
establishes the general-linear target only; the separate upper-unipotent
target remains a separate obligation.
