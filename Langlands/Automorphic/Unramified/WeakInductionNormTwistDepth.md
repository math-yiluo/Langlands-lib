# Ramification of the local twists under the idele-class norm

For a number-field extension and any finite place upstairs over a given place downstairs, `exists_principalUnits_subset_range_localUnitNorm` proves that the norm of each upper principal-unit subgroup contains a lower principal-unit subgroup. The normalized completion valuations scale by the ramification index, so the completion embedding sends lower principal units of a given depth into upper principal units of that depth. The norm of any embedded unit is its power by the local degree. The principal-unit power cofinality theorem then gives the contained lower subgroup.

`weakInductionNormTwistDepth` uses this lower subgroup to choose a depth before the Hecke character is specified. A character nontrivial at that depth is nontrivial on the norm image of the given upper subgroup. Its norm pullback therefore has conductor strictly greater than the prescribed upper depth. The argument allows ramified places of the extension and independent number-field universes.

This is the conductor comparison for the highly ramified norm-pullback twists in Henniart–Herb (1995), §8.16, printed p. 183, after (16). The registered source is `henniart-herb-1995-induction`, SHA-256 `5e753525048b08007d9605baa9019c8e792512887305ec2e39ae9c3bee6a963e`.
