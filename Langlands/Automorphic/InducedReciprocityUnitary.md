# Unitarity of induced reciprocity representations

Author: Worker 5134. Module `Langlands.Automorphic.InducedReciprocityUnitary`,
namespace `Langlands.ClassField.Global.RelativeWeilGroup`. Universes: `u` (the
number fields) and `uV` (the carrier universe of
`inducedReciprocityRepresentation`).

Setting: `c` is a fundamental class family, `h : FundamentalClass.Restriction c`,
and `F ⊆ E' ⊆ L` is a tower of number fields with `L / F` Galois.
`inducedReciprocityRepresentation c F E' L h ξ` (Library
`Langlands.Automorphic.WeakInductionAssociationStatement`) is
`Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` for a Hecke character `ξ` of `E'`. It is
induced along `restrictionInclusion` from the character line of
`reciprocityCharacter c E' L ξ`, that is `w ↦ ξ(transfer w)⁻¹`.

This module records that `S(X)` of Henniart (2000), §3.4, is unitary. Harris's
character `ξ` (Harris 1998, Proposition 4.8) satisfies `ξ = ξ⁻¹ ∘ c` on the CM
field `E'`. The module builds on `Langlands.Weil.Representation.UnitaryInduction`
and `Langlands.Global.HeckeConjugateInverseUnitary`.

## Definition: `unitaryInducedReciprocityRepresentation`

For a unitary Hecke character `ξ` (`hξ : ξ.IsUnitary`),
`unitaryInducedReciprocityRepresentation c F E' L h hξ` is
`inducedReciprocityRepresentation.{u, uV} c F E' L h ξ` bundled with its
unitarity, as an element of `{A // A.IsUnitary}`.

## Results

- `norm_reciprocityCharacter_apply`: for `K ⊆ L` Galois and `ξ` a unitary Hecke
  character of `K`, every value of `reciprocityCharacter c K L ξ` has absolute
  value `1`.
- `inducedReciprocityRepresentation_isUnitary`: if `ξ` is unitary, then
  `inducedReciprocityRepresentation.{u, uV} c F E' L h ξ` is unitary.
- `inducedReciprocityRepresentation_isUnitary_of_isConjugateInverse`: if `E'`
  is a CM field and `Harris.IsConjugateInverse ξ`, the same representation is
  unitary.

## Proofs

`norm_reciprocityCharacter_apply`: the value is `(ξ (transfer w))⁻¹`
(`reciprocityCharacter_apply`), and `‖z⁻¹‖ = ‖z‖⁻¹ = 1`.

`inducedReciprocityRepresentation_isUnitary`: the character line is unitary
(`FiniteRepresentation.characterLine_isUnitary`), and induction along an
injective map with finite-index range preserves unitarity
(`FiniteRepresentation.isUnitary_induceAlong`).

The CM case combines this with
`HeckeConjugateInverse.isUnitary_of_isConjugateInverse`.
