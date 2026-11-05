# Three-factor determinant balance for equal dynamic centralizers

Author: Worker 700.

`Dynamic.centralizingDeterminantSquareDefect` is the additive rational
character on the acting group given by the determinant on `U` plus the
determinant on `V` minus twice the determinant on their represented
intersection `C`. Its evaluation is the multiplicative discrepancy in the
desired square identity. Defining it requires the represented subgroups,
the centralizing acting map, affineness and finite Lie coordinates; it
requires no equality of centralizers or root-system assumption.

This internal deduction starts with two cocharacters `zeta` and `eta` of the
same split torus in an affine group scheme locally of finite type over an
arbitrary field. Equality of their dynamic centralizers means equality of
the complete subgroup functors, including every relative test scheme.

`latticePairing_eq_zero_iff_of_centralizer_eq` applies the published
`weightSpace_inf_tangentSubmodule_centralizer` to both sides of that equality.
For an actual nonzero weight space the two resulting conditional submodules
agree only if the pairings vanish together.
`regionWeightCharacter_positive_zero_eq_zero_of_centralizer_eq` therefore
annuls the positive/zero weighted region term by term. A zero weight space
has dimension zero; on a nonzero space, positive pairing for one cocharacter
excludes zero pairing for the other.

`HasRelativeRootSystem.positiveWeightCharacter_balance_of_centralizer_eq`
specializes the existing dimension-weighted sign balance and eliminates both
axes using these deductions. The actual relative-root-system hypothesis
supplies the opposite-weight multiplicity equality through the existing
balance theorem. No characteristic assumption is used.

For affine represented radicals `U` and `V` and their represented
intersection `C`, the acting affine group `Z` maps into both centralizers,
and the split torus factors through that map. The actions are precisely
`Dynamic.centralizingUnipotentAction` and
`Dynamic.centralizingUnipotentIntersectionAction`.
`characterRestrict_centralizingDeterminant_square_of_centralizer_eq` combines
the published determinant restriction formulas with the preceding weighted
identity. It proves an equality after restriction to the torus without
constructing representatives or Lie coordinates for either axis subgroup.
`characterRestrict_centralizingDeterminantSquareDefect_eq_zero` expresses
this equality as vanishing of the defined discrepancy after restriction.

`centralizingDeterminant_square_of_centralizer_eq` explicitly assumes
injectivity of `characterRestrict j` to deduce the character equality on all
of `Z`. Evaluating that equality gives
`rationalCharacterEval_centralizingDeterminant_square_of_centralizer_eq` at
every rational point of `Z`. These last two lemmas do not prove the
injectivity premise, reductivity of `Z`, or any central-torus detection
statement. They cannot supply the unconditional rational corrected-orbit
target until that premise has been discharged.
`centralizingDeterminantSquareDefect_eq_zero` records the corresponding
vanishing statement under exactly the same explicit injectivity premise.

The direct declaration dependencies are
`weightSpace_inf_tangentSubmodule_centralizer`,
`HasRelativeRootSystem.positiveWeightCharacter_balance`,
`regionWeightCharacter`, the two determinant restriction formulas just
named, and `rationalCharacterEval_add`. The remaining steps use equality
transport, finite dimension of the zero submodule, additive character
arithmetic and evaluation. This pair has derived provenance from those
Library declarations and cites no additional external structural input.
