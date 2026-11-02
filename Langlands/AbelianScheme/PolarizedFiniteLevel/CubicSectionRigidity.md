# Rigidity using a full basis of cubic-bundle sections

For an ordinary polarized finite-level datum over a field,
`Datum.cubicSectionMap` is the actual polynomial-Proj morphism defined by a
finite ordered basis of all sections of its cubic bundle, assuming generation
at every scheme point. It lies over the original field.
`Datum.cubicSectionMapTwistIso` constructs an actual isomorphism from the
pullback of the projective twist `O(1)` to that cubic bundle, by the existing
linear-system twist comparison.

For an actual polarized automorphism and an actual isomorphism from the
pulled-back cubic bundle to itself, `cubicSectionCoordinateEquiv` constructs
the coordinate linear equivalence on this projective space. The underlying
scheme map is an isomorphism and preserves the field structure map. Applying
`SectionAction.linearSystemMap_basis_equivariant` proves equivariance of the
actual cubic section map for this constructed equivalence.

Over an algebraically closed field, `hom_eq_id_of_cubicSectionBasis` assumes
positive level, monomorphy of this section map, a bound `q` on its actual
torsion sections in every nonzero linear hyperplane, and
`(m + 1) * q < n^(2*g)`. The existing torsion-configuration theorem and the
constructed equivariance prove that the underlying scheme endomorphism is
the identity. `eq_refl_of_cubicSectionBasis` then proves equality of the actual
polarized automorphism with its identity, including its level data.

`eq_refl_of_cubicSectionBasis_count` applies the exact published
`CubicTorsionHyperplaneBoundStatement` as a premise. It retains positive
dimension, polarization index and level, nonzero image of the level in the
field, closed immersion of the section map, nondegeneracy against every
nonzero homogeneous linear polynomial, and the strict inequality
`(m + 1) * (6^g * d * g! * n^(2*g-2)) < n^(2*g)`. The actual twist comparison
supplies the count statement's bundle identification, and the constructed
coordinate equivalence supplies its equivariant lift. The result is equality
of the actual polarized automorphism with the identity.

This is an internal composition of the actual section-action, twist-comparison
and torsion-configuration constructions. No new external source assertion is
used. Existence of the finite section basis, generation, preservation of the
cubic bundle by every polarized automorphism, the closed immersion,
nondegeneracy, the geometric count and its strict numerical range remain
separate obligations. This unit does not assert unconditional finite-level
rigidity or ordinary moduli representability.
