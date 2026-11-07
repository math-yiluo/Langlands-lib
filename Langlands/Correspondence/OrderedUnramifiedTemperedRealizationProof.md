# Ordered unramified principal series as tempered standard modules

Module `Langlands.Correspondence.OrderedUnramifiedTemperedRealizationProof`.
The theorem `Langlands.Correspondence.orderedUnramifiedTemperedRealization`
proves the unchanged proposition
`Langlands.Correspondence.OrderedUnramifiedTemperedRealizationStatement.{uF, uA} F`
from `Langlands/Correspondence/SphericalStandardModulePrerequisites.lean`. The
field universe `uF` and the block carrier universe `uA` stay independent.

The statement says the following. Let `F` be a p-adic field, `r` a natural
number and `z : Fin (r + 1) → ℂˣ` a tuple with
`Monotone (fun i => ‖(z i : ℂ)‖)`. Then there is a tempered Langlands datum
`d : TemperedLanglandsDatum.{uA, uF} F.canonicalTopologicalData (r + 1)` whose
actual standard module `d.standardModule.representation` is equivalent to
`Unramified.principalSeriesOfTuple F z`. There are no further hypotheses. The
proof constructs the datum from the maximal runs of equal norm.

The proof is an internal derivation from published Library results. It
groups equal exponents in the Langlands classification, for unramified
principal series. It uses the helper module
`Langlands.Representation.Unramified.UnitaryPrincipalSeriesBlocks`, whose
Markdown explains the block facts used in step 3.

## Auxiliary results in this module

- `normRank z a` counts the coordinates `c` with `‖z c‖ < ‖z a‖`.
  `normRank_le_iff` proves that `normRank z a ≤ normRank z b` exactly when
  `‖z a‖ ≤ ‖z b‖`. The strict direction uses a strict inclusion of the counted
  sets.
- `exists_normShape`: for weakly increasing norms, `normRank z` is monotone,
  and the published `Geometric.monotoneBlockShape` gives a block shape
  `D : BlockShape (r + 1)` with
  `blockIndex D a ≤ blockIndex D b ↔ ‖z a‖ ≤ ‖z b‖`. Coordinates therefore lie
  in the same block exactly when their norms agree, and earlier blocks have
  strictly smaller norms.
- `uniformizer_norm_bounds`: `0 < |ϖ| < 1` for the normalized absolute value
  of the chosen uniformizer. It follows from `normalizedAbs_uniformizer`
  (`|ϖ| = q⁻¹`) and `residueCardinality_gt_one`.
- `norm_realPowerCharacter_uniformizer`: the uniformizer value of `|·|^s` has
  norm `|ϖ|^s`.
- `rankOneCharacterObject_representation_eq`: if `z = c_s · w`, where `c_s`
  is the uniformizer value of `|·|^s`, then the rank-one character object of
  `z` is the `|det|^s` twist of that of `w`, as an equality of actual
  representations. The proof combines `realPowerDeterminant_eq_unramifiedCharacter`
  with `determinantUnramifiedCharacter_mul`.
- `realPowerSmoothCharacter F s` is `|·|^s` as a smooth field character. Its
  kernel is open by `isOpen_ker_realPowerCharacter`.
- `blockTwistEquiv`: let `X` be any realization of `unitaryBlock F wb`, and
  suppose `zb k = c_s · wb k` for every `k`. Then it constructs an actual
  equivalence from the normalized principal series of the rank-one objects of
  `zb` to `segmentFactor X s`. It composes three equivalences:
  - the factorwise equalities above, through `normalizedProductInducedEquiv`;
  - the inverse of the common determinant twist,
    `normalizedProductDeterminantTwistEquiv`;
  - the twist of the given equivalence, `twistEquiv`.

## Proof of the theorem

1. **Runs.** `exists_normShape` gives the outer shape `D`.
2. **Exponents.** For block `j`, let `first j` be its first coordinate. Put
   `u j = log_{|ϖ|} ‖z (first j)‖` (`Real.logb`). Norms strictly increase
   across blocks, and `log_{|ϖ|}` strictly decreases because `|ϖ| < 1`
   (`Real.logb_lt_logb_of_base_lt_one`). So `u` is strictly decreasing, as the
   datum requires. Let `c j` be the uniformizer value of `|·|^(u j)`. Then
   `‖c j‖ = |ϖ|^(u j) = ‖z (first j)‖` (`Real.rpow_logb`).
3. **Unitary parameters and blocks.** Put `w i = z i · (c (blockIndex D i))⁻¹`.
   Coordinates in one block have equal norms, so `‖w i‖ = 1`; also
   `z i = c j · w i` for `i` in block `j`. The block of `j` is
   `unitaryBlock F (wb j)`, where `wb j k = w (D.index j k)`. It is irreducible
   and analytically tempered by `unitaryBlock_isIrreducible` and
   `unitaryBlock_isTempered`.
4. **Carrier universe.** The published `padicIrreducibleSmoothSmallRealization`
   gives, for each block, an equivalent irreducible smooth realization
   `blk j` with carrier in `Type uA`. Temperedness transports along the
   equivalence (`isTempered_iff_of_equiv`). The datum `d` has shape `D`,
   blocks `blk`, exponents `u`, and the proved irreducibility, temperedness
   and `StrictAnti` fields.
5. **Standard module.** Refine `D` by the shapes `BlockShape.singletons (D.size j)`, and
   use the block numbering `D.indexEquiv` into the coordinates of
   `borelShape r`. The coordinate compatibility required by ordered
   regrouping follows from `BlockShape.singletons_index`: the inner and the Borel indices
   are the identity. The fine factors are the rank-one objects
   `rankOneCharacterObject F (character F (z i))`. For each block `j`,
   `blockTwistEquiv` identifies the inner product with the actual twisted
   block `twistedBlocks D blk u j = segmentFactor (blk j) (u j)`. The published
   `normalizedProductRegroupingToEquiv` (with
   `Parabolic.orderedProductRegrouping`) then turns these into an equivalence
   from the Borel normalized product of the fine factors to
   `T.normalizedProductInduced D` of the twisted blocks. The latter is
   `d.standardModule.representation` by `standardModule_representation`.
6. **Principal series.** `principalSeriesOfTuple F z` is the Borel normalized
   product of `characterRepresentation (determinantQuasiCharacter F 1 (character F (z i)))`.
   The fine factors are the same characters on `ULift ℂ`.
   `normalizedProductInducedEquiv`, with the factorwise `ULift.moduleEquiv`,
   compares the two products. Composing the inverse of step 5 with this
   comparison gives the required equivalence.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. It assumes no classification, irreducibility, temperedness or
standard-module comparison premise. Equal-norm runs are handled by the
irreducibility and temperedness proofs of step 3. The ordering comes from the
monotone norms, so the conclusion is the ordered presentation the statement
asks for, not an arbitrary reordering of a reducible principal series.
