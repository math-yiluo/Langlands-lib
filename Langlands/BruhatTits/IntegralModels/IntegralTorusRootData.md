# Root-model data from the supplied integral torus

This internal interface connects the supplied `IntegralTorusData D S i`
of the facet axioms with `IntegralSplitTorusData D.neutral i`, the input
used to construct integral root models. The base is an arbitrary domain
`R` with fraction field `K`, and the universe is arbitrary.

`IntegralTorusData.toIntegralSplitTorusData T hT` retains the actual integral
torus `T.torus`, its actual inclusion `T.inclusion` into `D.neutral.group`,
and the specified generic identification `T.genericIso`. The published
`CommGroupScheme.isoOfGroupIso` expresses that same group isomorphism in
the commutative-group category. The commuting generic square is precisely
`T.generic_comm`. The supplied hypothesis `hT` asserts that the integral
torus is split; closedness and special-fibre maximality are not needed.

The three accompanying equalities are definitional equalities of these
published constructions. The integral character used by the root model is
the inverse of `T.genericCharacterEquiv hT`. Over a local domain, the
special-fibre inclusion is the same actual residue-base change of
`T.inclusion`, and the generic-to-residue character equivalence is exactly
`T.characterSpecialization hT` from `FacetLieWeights`. In particular, using
the root-model interface introduces no choice of a different lattice
identification in the facet sign formula.

This is an internal comparison of existing data structures and actual
maps. It does not assert existence of a torus or prove the facet sign
formula, root survival, or descent.
