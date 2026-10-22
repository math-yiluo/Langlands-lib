# Character, determinant, twist and dual compatibility conditions

Author: Worker 7. This module states the conditions relating a correspondence
family to local class field theory and to the operations on both sides:
rank-one reciprocity, determinant against central character, twists by
quasi-characters, and contragredients. It gives them for the full family
(`FullMap` of `Domains`) and, separately, for the irreducible-Weil to
supercuspidal family (`SupercuspidalMap`). The conditions are propositions on
a given family; no family is constructed and no part of LLC is asserted.

## Reciprocity

Every condition except duality depends on a reciprocity candidate `e`.
`ReciprocityCandidate F` is the published `LocalFactor.RankOne.ReciprocityCandidate F`:
a topological group isomorphism from the abelianization of the local Weil
group to `Fˣ`, for the canonical topology of `F`. `IsGeometricReciprocity F e`
is the published `LocalClassField.GeometricWeilReciprocityRelation` at the
canonical topology. It says that the valuation of `e` at an element equals
that element's geometric degree, so a geometric Frobenius goes to an element
of valuation one, and that `e` induces the geometrically normalized finite
norm-residue maps. This module does not assume that such an `e` exists or is
unique. The correspondence predicate built from these conditions must require
`IsGeometricReciprocity F e` and quantify `e` existentially; it must not take
`e` as an input.

`reciprocityHom F e` is the map `W_F → Fˣ` obtained by composing the
abelianization projection with `e` (published `reciprocityUnits`).
`weilCharacter F e χ` pulls a quasi-character `χ : Fˣ → ℂˣ` back to the Weil
group (published `LocalFactor.RankOne.weilCharacter`). Two definitional
lemmas identify it: `weilCharacter_eq_symm` with the inverse of the published
character transport `weilCandidateCharacterEquiv`, and `weilCharacter_eq_comp`
with `χ ∘ reciprocityHom F e`.

## Determinants and rank-one characters

`parameterDeterminant F D` is the determinant character of the Weil
representation underlying a parameter class `D`. It is defined on
representatives and descends because equivalent representations have equal
determinant characters (published `determinantCharacter_eq`). The monodromy
plays no role. `irreducibleWeilDeterminant F σ` is the published
`determinantCharacterClass` of an irreducible Weil class.

`IsRankOneParameterCharacter F χ D` says that the rank-one parameter class
`D` is the class of the pair `(χ, 0)`, for a character `χ` of the Weil group:
some pair representing the underlying class of `D` is equivalent to the
zero-monodromy pair on the one-dimensional representation given by `χ`.
`IsRankOneWeilCharacter F χ σ` says the same for an irreducible Weil class,
without monodromy.

## Full-family conditions

For a full map `c` and a reciprocity candidate `e`:

- `RankOneCompatibility F e c`: for every quasi-character `χ` of `Fˣ` there
  is a rank-one parameter class `D` that is the class of
  `(χ ∘ reciprocityHom F e, 0)`, and `c 1 D` is the class of the character
  `χ ∘ det` of `GL_1(F)`.
- `DeterminantCompatibility F e c`: for every rank `n`, class `D` and Weil
  element `w`, the scalar matrix `reciprocityHom F e w · 1` acts on `c n D`
  by `parameterDeterminant F D w`. This is the identity
  `ω ∘ reciprocityHom F e = parameterDeterminant F D` for the central
  quasi-character `ω` of `c n D`, stated pointwise so that the existence of
  `ω` is not assumed.
- `TwistCompatibility F e c`: for every `n`, `D` and quasi-character `χ`,
  there is a parameter class `E` of rank `n` that is the twist of `D` by
  `χ ∘ reciprocityHom F e` (published `ParameterRelations.IsTwistOf`, which
  twists the Weil action and keeps the monodromy), and `c n E` is the twist
  of `c n D` by `χ ∘ det` (`IsCharacterTwist`).
- `DualCompatibility F c`: for every `n` and `D`, there is a parameter class
  `E` that is the dual of `D` (published `ParameterRelations.IsDualOf`, with
  dual action and monodromy `-Nᵀ`), and `c n E` is the smooth contragredient
  of `c n D` (`IsSmoothDual`).

The twisted and dual parameter classes are asserted to exist inside the
conditions, so the conditions cannot hold vacuously. The closure of the
parameter domain under these operations is not assumed; it is the subject of
the separate, unproved statement targets `DualExistence` and
`TwistPreservation` in the published
`Langlands.WeilDeligne.ParameterRelationStatements`. Twists are by arbitrary
quasi-characters, with no unitarity or finite-order condition.

## Supercuspidal-family conditions

For a supercuspidal map `c` and a reciprocity candidate `e`:

- `SupercuspidalRankOneCompatibility F e c`: for every `χ` there is a rank-one
  irreducible Weil class `σ` that is the class of `χ ∘ reciprocityHom F e`,
  and `c 1 σ` is the class of `χ ∘ det`.
- `SupercuspidalDeterminantCompatibility F e c`: the scalar matrix
  `reciprocityHom F e w · 1` acts on `c n σ` by
  `irreducibleWeilDeterminant F σ w`.
- `SupercuspidalTwistCompatibility F e c`: `c n` of the twist of `σ` by
  `weilCharacter F e χ` is the twist of `c n σ` by `χ ∘ det`. The twist of
  `σ` is the published bijection `FiniteRepresentation.continuousIrreducibleTwistEquiv`,
  so it is always defined.
- `SupercuspidalDualCompatibility F c`: `c n` of the dual of `σ` is the smooth
  contragredient of `c n σ`. The dual of `σ` is the published bijection
  `FiniteRepresentation.continuousIrreducibleDualEquiv`.

The automorphic sides use the restricted relations of
`SupercuspidalRelations`, which compare images in the full class space.
Because the outputs `c n (…)` are supercuspidal classes, these conditions
imply that the twist and the contragredient of each class in the image of
`c n` are again supercuspidal; they do not assume it.

## Sources and provenance

Henniart 2000, section 1.1, printed p.439 (PDF p.1), normalizes the
reciprocity map `τ_F : W_F → Fˣ` so that geometric Frobenius elements
correspond to uniformizers; its footnote 1 defines quasi-characters as
continuous homomorphisms to `ℂˣ`. Section 1.2, printed p.440 (PDF p.2),
states for the supercuspidal family: (1) `ω_{π(σ)} ∘ τ_F = det σ`;
(2) `π(σ ⊗ (χ ∘ τ_F)) = (χ ∘ det) π(σ)` for every quasi-character `χ` of
`Fˣ`; (3) `π(σ^∨) = π(σ)^∨`. Section 1.3, printed p.440, states that in rank
one the bijection is given by local class field theory. The four
supercuspidal conditions formalize (1)–(3) and section 1.3.

For the full family, Harris–Taylor 2001, Introduction, printed pp.1–2 (PDF
pp.9–10), normalizes `Art_K` so that geometric Frobenius elements correspond
to uniformizers, and lists the properties of a local Langlands correspondence
between Frobenius-semisimple Weil–Deligne representations and irreducible
admissible representations of `GL_n(K)`: rank-one class field theory
(property 1), twists by characters of `GL_1(K)` (property 3), determinant
against central character (property 4) and contragredients (property 5).
Harris–Taylor state these for `rec_K`, from representations to parameters;
the conditions here are the same identities for the inverse direction. Henniart
2002, section 1.1, printed p.588 (PDF p.2), uses the same reciprocity
normalization for `G(1) → A(1)`; section 2.9, printed p.596 (PDF p.10),
states `π(σ^∨) = π(σ)^∨` for the full family; section 2.5, printed p.595
(PDF p.9), defines the twist `χπ`.

Tate 1979, section 1.4.1, printed p.6 (PDF p.15), fixes the sign convention
that uniformizers correspond to the inverse of the arithmetic Frobenius, and
section 4.1.2, printed p.20 (PDF p.29), defines the Weil–Deligne pairs whose
twists and duals are used here.

- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Pair `L`- and `ε`-factor compatibilities and the unramified normalization
are not part of this module; they are separate modules of this task.

The module imports, and does not copy, these published declarations:
`Langlands.LocalFactor.RankOne` (`ReciprocityCandidate`, `reciprocityUnits`,
`weilCharacter`), `Langlands.ClassFieldTheory.Local.WeilReciprocityStatement`
(`GeometricWeilReciprocityRelation`, `weilCandidateCharacterEquiv`),
`Langlands.Weil.Representation.Determinant` (`determinantCharacter`,
`determinantCharacterClass`), `Langlands.Weil.Representation.TwistClasses`
and `Langlands.Weil.Representation.DualClasses` (the twist and dual
bijections of continuous irreducible classes) and Worker 1's
`Langlands.WeilDeligne.ParameterRelations` (`IsTwistOf`, `IsDualOf`). The
automorphic relations come from this task's `AutomorphicRelations` and
`SupercuspidalRelations`.

## Validation

The module compiles in the project Lean service without errors or warnings,
together with `Domains` and `SupercuspidalRelations`. Every condition returns
`Prop`.
