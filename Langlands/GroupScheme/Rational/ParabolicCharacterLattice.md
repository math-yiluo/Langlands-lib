# Finiteness of the rational characters of a presented parabolic

Module `Langlands.GroupScheme.Rational.ParabolicCharacterLattice` proves that
the rational character group `X^*(P)` of a parabolic subgroup `P` of a
connected reductive group, presented by a `ParabolicRootPresentation`, is a
free `ℤ`-module of finite rank. As a consequence the complex parameter space
`X^*(P) ⊗ ℂ` of the Eisenstein-series statements is finite-dimensional. That
is a hypothesis of the Library's notion of meromorphy in linear coordinates
(`IsMeromorphicInCoordinatesOn`).

## Provenance

Internal to the Library. The published theorem `rationalCharacterLattice`
(module `Langlands.GroupScheme.Rational.CharacterLatticeProof`) states this
finiteness for connected reductive groups. Its proof uses only that the group
is affine, smooth and connected: the characters are units of the coordinate
ring, they are linearly independent, and they lie in a finitely generated
subalgebra. A parabolic `P` is in general not reductive, so the published
statement does not apply to it directly. The module repeats the proof under
the weaker hypotheses and checks that a presented parabolic satisfies them.
The finiteness of the character group of a connected linear algebraic group
is a standard fact; no literature statement is reproduced, and the Lean proof
follows the published Library proof.

## Declarations

- `rationalCharacters_free_finite_of_smooth`: over a field `k`, if
  `G` is a group scheme over `Spec k` with `G → Spec k` affine and smooth and
  `G` connected, then `rationalCharacters G` is a free and finite
  `ℤ`-module. The proof is the body of `rationalCharacterLattice` with the
  reductivity hypothesis replaced by these three instances. The coordinate
  ring `D` is a domain (`isDomain_coord`). The map
  `χ ↦ unit χ ∈ D ⊆ Frac D` is a multiplicative map whose image is linearly
  independent over `k` (`linearIndependent_unit`, transported along the
  injective map `D → Frac D`). The images of a finite set of algebra
  generators of `D` (`Lie.coordinateAlgebraFiniteType`) generate a subalgebra
  containing all characters. The published lemma `free_and_finite` then
  gives freeness and finiteness.

- `ParabolicRootPresentation.connectedSpace`: for a presentation
  `r : ParabolicRootPresentation p l a` with `G` affine, locally of finite
  type and connected, the underlying space of `P` is connected. The field
  `r.isCompatible.realization` gives a cocharacter `ζ` with
  `range p = Dynamic.parabolic (ζ ≫ i)`. So `p` represents the dynamic
  parabolic `P_G(ζ)`, and `DynamicBaseConnected.connectedSpace_parabolic`
  (module `Langlands.GroupScheme.Dynamic.BaseConnectedProof`) says that a
  group scheme representing a dynamic parabolic of a connected affine group
  of finite type is connected. The representability of the range uses
  `r.isCompatible.parabolic.isClosedSubgroup`.

- `ParabolicRootPresentation.rationalCharacters_free_finite`: if moreover
  `G` is connected reductive and `P` is affine, then `rationalCharacters P`
  is free and finite over `ℤ`. Smoothness of `P` is the field
  `IsParabolicSubgroup.smooth` of `r.isCompatible.parabolic`. Connectedness
  is the previous lemma, applied with the smoothness and connectedness of `G`
  that `IsConnectedReductive` supplies. The result then follows from
  `rationalCharacters_free_finite_of_smooth`.
