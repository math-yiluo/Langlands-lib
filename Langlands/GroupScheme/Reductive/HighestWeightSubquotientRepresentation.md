# The highest-weight subquotient representation

This module realizes Tits's subquotient `X/Y` as an actual representation and
proves that it is irreducible of highest weight `ν` (Tits, *Représentations
linéaires irréductibles d'un groupe réductif sur un corps quelconque*,
J. reine angew. Math. 247 (1971), §3.4, Proposition 3.4: the module `X/Y` is
absolutely simple with weight `λ`). Here `X = highestGenerated ρ ν` and
`Y = highestRadical ρ ν` (module `HighestWeightSubquotient`). The weight `ν` is
assumed to have multiplicity one and to dominate every weight of `ρ`. This is
a special case of Tits's hypotheses, which allow strictly higher weights in
`ρ`; `Reductive/HighestWeightMaximalSubquotient` weakens domination to
maximality.

## Intertwiners and weight spaces

- `MatrixRepresentation.Intertwines.mem_characterSpace_of_leftInverse`: an
  intertwiner `C` with a left inverse reflects character vectors. If `C v` is a
  character vector, so is `v`. Apply the left inverse to the character
  equation of `C v` on every affine test.
- `SplitPinning.Intertwines.restrict_inclusion`: intertwiners restrict to the
  torus.
- `SplitPinning.Intertwines.mulVec_mem_weightSpace`,
  `mem_weightSpace_of_leftInverse` and `map_weightSpace_le`: intertwiners map
  weight spaces into weight spaces, and left-invertible ones reflect weight
  vectors.
- `map_weightSpace_eq_of_surjective`: a surjective intertwiner maps each weight
  space onto the corresponding weight space. The images sum to everything, so
  the independence lemma `iSupIndep.eq_of_le_of_iSup_eq_top` (module
  `TensorWeights`) applies.
- `map_weightSpace_eq_inf_range`: a left-invertible intertwiner maps a weight
  space onto the target weight space intersected with its range.
- `finrank_map_of_disjoint`: a linear map whose kernel meets a subspace
  trivially preserves its dimension.

## The subquotient

- `HighestSubquotientData ρ ν` records split coordinates of `X/Y`:
  - a subrepresentation `sub` with inclusion `incl` (range exactly `X`) and
    left inverse `retr`;
  - a quotient `quot` of `sub` with projection `proj` (kernel exactly the
    preimage of `Y`) and section `sect`;
  - both intertwining identities.
- `nonempty_highestSubquotientData`: such data exist for an affine group. The
  published split coordinates (`exists_subspace_split_coordinates`,
  `isStableCoordinates`, `restrictCoordinates`, `intertwines_restrictCoordinates`,
  `range_coordinateInclusion_eq`) give the subrepresentation on the stable
  subspace `X`. The published `nonempty_quotientRepresentation` gives its
  quotient by the stable preimage of `Y`.
- `HighestSubquotientData.isHighestWeight`: under the multiplicity-one and
  domination hypotheses, `quot` is a representation of highest weight `ν` in the
  published sense `IsHighestWeight`. It checks the four defining conditions.
  - Irreducibility: a stable subspace `W` of `quot` pulls back and pushes
    forward to a stable subspace of `ρ` between `Y` and `X`. By
    `eq_highestRadical_or_eq_highestGenerated` that subspace is `Y` or `X`, so
    `W = 0` or `W = everything`.
  - The weight spaces of `quot` span (published `iSup_representationWeightSpace_eq_top`).
  - The `ν` weight space of `quot` is one-dimensional. The `ν` weight space of `ρ`
    lies in `X`, its preimage under `incl` is a line, and that line meets the
    kernel of `proj` trivially because `Y` avoids the weight `ν`.
  - Every weight of `quot` is a weight of `ρ`, hence is dominated by `ν`.

No hypothesis on the field or its characteristic is made.
