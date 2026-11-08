# Coefficient changes for weighted Hermitian matrix groups

This internal algebraic construction treats two arbitrary commutative rings,
with independent coefficient and finite-index universes. A coefficient
homomorphism must commute with the specified involutions and carry every
weight of the source diagonal form to the corresponding target weight.

Entrywise calculations prove compatibility of the Gram matrix and conjugate
transpose with this map. Mapping the full Gram preservation equation then
proves `preservesForm_map`. The induced general-linear group homomorphism
preserves determinant one, giving `specialUnitaryMap` on the actual
determinant-one isometry subgroups. This construction does not require
unit weights. Its underlying matrix is exactly entrywise coefficient change.

For source and target forms equipped with actual unit weights,
`map_gramElement` identifies the mapped invertible Gram element with the
target Gram element. The target unit witnesses need only have the prescribed
values; they are not required as additional equality data to be mapped
source witnesses. The proof uses equality of underlying matrices and the
extensionality of units.

Conjugate transpose on special-linear matrices also commutes with coefficient
change. The usual inclusion into the general-linear group commutes with the
map, so the formula for the inverse-adjoint twist proves `unitaryTwist_map`
by multiplicativity and compatibility with inversion. This yields the
homomorphism `twistFixedMap` on the actual fixed subgroups. The theorem
`fixedSpecialUnitaryEquiv_map` states that the earlier fixed-point/isometry
comparison respects these coefficient maps.

For a ring equivalence, applying its injectivity proves compatibility of
the inverse with the involutions and weights. Applying the two coefficient
maps in opposite directions then gives `twistFixedRingEquiv` and
`specialUnitaryRingEquiv`. Their inverses are checked entry by entry.
The latter equivalence also acts on its underlying matrix by the original
ring equivalence.

The provenance is direct internal matrix algebra, using the previously
constructed full Gram form, determinant-one isometry group and genuine
inverse-adjoint twist. There is no characteristic, anisotropy, or field
hypothesis. Actual scheme construction, rational-point comparison, root
dynamics and the unrestricted local Kneser–Tits theorem remain separate.
