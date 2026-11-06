# Actual rank-one supercuspidal character classes

This internal construction uses the published universe-lifted
`FiniteRepresentation.characterLine` to represent a continuous field
quasicharacter on `ULift.{uA} ℂ`. The field universe `uF` and representation
carrier universe `uA` remain independent.

The private irreducibility helper uses the published rank-one dimension of
the line and Mathlib's simplicity of the submodule lattice in dimension one.
The invariant-submodule lattice inherits this simplicity by the injective
map to ordinary submodules. Smoothness follows from the proved open-kernel
theorem for continuous complex characters on nonarchimedean groups, applied
to the character composed with the continuous determinant. Its open kernel
fixes every vector of the line. Fixed-vector spaces are finite dimensional
as submodules of the line, giving the all-open-subgroups admissibility
required by the existing definition.

`isSupercuspidal_rankOne_iff` proves that the actual supercuspidal condition
in GL₁ is just admissibility. Every block shape has at most one block.
Consequently no two block indices are in strict order, so the defining
upper-block-triangular condition imposes no restriction and every block
parabolic is the whole group.

`rankOneCharacterObject` bundles the smooth line.
`rankOneSupercuspidalObject` bundles its irreducibility and supercuspidality,
and `rankOneSupercuspidalClass` takes its genuine isomorphism class.
`rankOneSupercuspidalClass_spec` proves the existing
`IsSupercuspidalRankOneCharacter` relation using the published equivalence
between the lifted line and the scalar model on `ℂ`.

`exists_rankOneAutomorphicCharacter` applies the published
`GodementJacquet.exists_tateCharacterModel` to an actual representative of
the given irreducible admissible smooth class. It makes no extra dimension,
Whittaker or central-character assumption. This classification together
with the existing uniqueness of classes for a fixed scalar character
proves surjectivity of the constructed supercuspidal character-class map.

This is derived from existing Library constructions and proved facts. It
does not construct reciprocity or higher-rank correspondence, nor assert
any local-factor compatibility.

The scalar-line irreducibility proof is reused from
`FiniteRepresentation.characterLine_isIrreducible` in
`Langlands.Correspondence.AssemblyEpsilonSystemHelpers`.
