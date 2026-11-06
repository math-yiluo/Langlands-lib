# Finite norm quotients for norm-subgroup existence

Worker 1766 derives this auxiliary construction and its support results from the published,
unconditional local class-formation realization. They are part of work toward
`Langlands.LocalClassField.NormSubgroupExistence`; they do not yet prove that
proposition or assert that arbitrary open subgroups are norm groups.

For a finite Galois extension of the carrier of a p-adic field, take the unique
fundamental class supplied by `localAbsoluteCorestrictionCompatibleClassFormation`.
Its Tate cup map in degree minus two is bijective. The existing
`abelianizationCupEquiv` therefore identifies the actual finite Galois
abelianization with the quotient by the determinant-norm image. Transport
finiteness along this equivalence to prove finite index. For an abelian
extension, its Galois group equals its abelianization, so the cardinality of the
quotient equals the field degree by the finite Galois cardinality theorem.

All fields in this unit have arbitrary common universe `u`, and all norms and
quotients are the Library's actual constructions. No reciprocity map or
class-formation witness is supplied as an added hypothesis.

`finiteNormAbelianizationEquiv` chooses one such multiplicative equivalence by
classical choice. Its inputs are the p-adic field and the finite Galois extension;
the class-formation witness and fundamental class are obtained inside its
construction. This auxiliary choice is used only to transport finiteness and
cardinality. This unit asserts no normalization, continuity, or compatibility
with restriction or norm maps for the chosen equivalence. In particular, it is
not a constructed finite reciprocity system.

This is derived content: the proof uses the published local class formation,
the published Tate comparison equivalence, Mathlib's abelianization of a
commutative group, and its finite Galois cardinality theorem. No additional
source theorem is postulated.
