# Nondegeneracy for the complete cubic linear system

For an ordinary polarized finite-level datum over any field and a specified
finite ordered basis of all sections of its cubic bundle,
`Datum.cubicHyperplaneSectionEquiv` associates to each actual homogeneous
linear polynomial the actual cubic-bundle section with the same basis
coefficients. This is the specialization of `basisHyperplaneSectionEquiv`
to the datum's cubic bundle.

If the basis generates at every scheme point,
`Datum.cubicSectionMap_nondegenerate` proves that every nonzero homogeneous
linear polynomial is absent from the homogeneous prime ideal of some point
in the image of the actual cubic section map. The abelian scheme is integral
by the published `field_isIntegral`, hence reduced. The generic complete
linear system nondegeneracy theorem then applies. Reducedness is derived
from the datum and is not an additional premise.

Over an algebraically closed field,
`Datum.cubicSectionMap_torsionHyperplane_bound` applies the exact supplied
`CubicTorsionHyperplaneBoundStatement`. It assumes positive dimension,
polarization index and level, nonzero image of the level in the field,
generation of the section basis, and closed immersion of the cubic section
map. Its twist comparison and nondegeneracy are constructed internally.
For every nonzero homogeneous linear polynomial it bounds the actual
torsion sections in its hyperplane by `6^g * d * g! * n^(2*g-2)`.

`PolarizedIso.eq_refl_of_nondegenerate_cubicSectionBasis_count` applies the
existing section-basis rigidity theorem with this derived nondegeneracy.
It retains an actual pullback isomorphism of the cubic bundle and the strict
size inequality
`(m + 1) * (6^g * d * g! * n^(2*g-2)) < n^(2*g)`.
It proves equality of the actual polarized automorphism with its identity.
The coordinate lift is constructed by the imported section-action theorem.

This is an internal specialization and composition of the published
abelian-scheme geometry and the generic complete linear system and
cubic-section constructions. It introduces no new external source assertion.
Existence of the finite full basis, generation, the closed immersion, the
bundle transport, the geometric count and its strict numerical range remain
separate obligations. The geometric count is a premise here. This unit
does not establish unconditional rigidity or ordinary moduli representability.
