# Actual Lie frames for relative parabolic families

For a homomorphism `j : P ⟶ G` of group schemes over an arbitrary
`S : Scheme.{u}`, `IsRelativeParabolicSubgroup.lie_hasFiniteLocalBasis`
uses the smoothness field of the actual relative parabolic predicate
to obtain finite local bases of `P.Lie`. This is the internal Lie
sheaf defined as the dual of the cotangent sheaf at the identity.
No reductivity or additional rank or freeness hypothesis is required.

For any actual `ParabolicRepresentative r` of a parabolic subgroup
functor, `r.lie_hasFiniteLocalBasis` specializes the same result to
`r.group.Lie`. `r.lieFiniteLocalBasisData` exposes the generic proved
smooth-group frame data, with its local freeness, finite type and
finite basis index instances. `r.lieFiniteLocalBasisTrivialization`
gives an actual free-sheaf isomorphism on each open of that cover.
These constructions also apply to the chosen
`parabolicRepresentative F`; they do not replace its actual group by
an abstract module or a dual-number module.

This module is an internal specialization of
`Langlands.GroupScheme.Lie.FiniteLocalFrames` to the published actual
relative parabolic predicate and presheaf representative structures.
It introduces no literature translation. It supplies finite local
frames for determinant constructions; it does not construct a
determinant, prove coherence under changing representatives or base
change, establish ampleness, or prove global parabolic representability.
