# Evaluation of maps from a transitive action

This is an internal elementary group-action construction for the Harris raw
level comparison. It uses Mathlib's actual `MulActionHom` and
`MulAction.IsPretransitive`, with independent universes for the group, source
and target. It does not invoke a geometric classification or literature theorem.

For a group acting on types `X` and `Y`, fix `x : X`. A value in `Y` is
stabilizer-fixed if every group element fixing `x` fixes that value.
`smul_eq_of_stabilizer_fixed` proves that two elements carrying `x` to the
same point also carry a stabilizer-fixed value to the same value: their ratio
fixes `x`, and multiplication by the second transporter proves the equality.

Assuming the action on `X` is pretransitive,
`equivariantMapOfStabilizerFixed` chooses a transporter from `x` to each point
of `X` and applies it to the prescribed value. The preceding equality shows
that this function commutes with the group action.
`equivariantMapOfStabilizerFixed_apply` proves its value using any specified
transporter, independently of the chosen one.

`transitiveActionEvaluationEquiv` identifies actual equivariant maps `X →[G] Y`
with the full subtype of stabilizer-fixed values at `x`. Its forward map is
literal evaluation. Equivariance gives fixedness and the first inverse law;
the transporter formula at the identity gives the second inverse law.
`equivariantMap_evaluation_injective` records uniqueness from one value.

No finiteness, topology, cover, connectedness or surjectivity of a group map is
assumed or concluded. In particular, this lemma alone does not identify a
geometric stabilizer with the image of a cover fundamental group.
