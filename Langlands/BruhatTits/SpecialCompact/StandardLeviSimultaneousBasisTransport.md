# The simultaneous standard basis on a representing Levi scheme

`SimultaneousStandardBasisAt.leviScheme` restricts a supplied simultaneous
standard basis of a connected reductive group to its actual standard Levi
scheme for a set `J` of simple roots. The common subgroup is the preimage
`leviSchemeCompact K0 i ν J` of the original subgroup `K0`. The single family
`leviSchemeBasisFamily` consists of the preimages of the original members
under the rational points of the representing Levi inclusion.

The rational-point inclusion is a closed embedding. It factors through the
canonical multiplicative homeomorphism onto the closed subgroup of actual
standard Levi points. For a closed group embedding, preimages preserve
inclusion in the normalizing subgroup, normality there, openness and
compactness. The induced topology transports the neighborhood basis at the
identity. The inherited family for each inner standard Levi follows by
intersecting this pulled-back family with that closed subgroup.

The intrinsic simple roots of the outer Levi are `J`. Thus each face `R` of
the outer Levi is an ambient standard face and the corresponding ambient
split component is available. `IsCompatibleStandardSplitComponent.leviScheme`
keeps that component and its map into the original torus. The theorem
`StandardParabolicBasisMember.leviScheme` supplies ordered decomposition,
contraction and cofinality for the preimage of every original basis member.

This is a derived structural input for applying the intrinsic Xi estimates
to a standard Levi. It uses the published member-level restriction and
preserves the ambient choice of family and split components. Levi Iwasawa and
Cartan coverings enter the analytic estimates through their own hypotheses.

The shared restriction theorem uses the same preimage family. [Standard Levi basis inheritance](StandardLeviBasisInheritance.md)
