# Concrete automorphic relations for the correspondence

Author: Worker 7. This module defines the automorphic side of the local
Langlands correspondence for `GL_n(F)`: the actual class space, and the
operations on it that the correspondence must match (central action,
character twist, smooth contragredient, and rank-one characters). It states
no part of LLC.

## Objects and classes

`AutomorphicObject F n` instantiates the published irreducible admissible
subcategory `IrreducibleAdmissibleRep` with complex coefficients, the actual
matrix group `GeneralLinear n F.Carrier`, and its canonical topology
`F.canonicalGeneralLinearTopology n`. `AutomorphicClass F n` is the published
quotient `SmoothDualClass` of these objects by isomorphism. The prime, the
finite extension `F`, the positive rank `n : ℕ+` and an independent
representation-carrier universe are parameters. No finite-dimensionality,
genericity or extra topology is imposed on the carrier, so the class space
contains every irreducible admissible representation, not only the
supercuspidal or generic ones.

`automorphicClassOf` is the quotient map. Two certificates show that the class
space is the genuine one: every class has a representative
(`automorphicClass_has_representative`), and two representatives give the same
class exactly when their actions admit an equivariant linear equivalence
(`automorphicClassOf_eq_iff`).

## Operations

`QuasiCharacter F`, imported from `LocalConventions`, consists of all
continuous homomorphisms `Fˣ → ℂˣ`, with no unitarity condition.

- `determinantQuasiCharacter F n χ` is `χ ∘ det` on `GL_n(F)`.
- `CentralActsBy π a z` says that some representative of `π` has the scalar
  matrix `a·1` acting by the scalar `z`. It does not assume that a central
  character exists.
- `IsCharacterTwist F χ π π'` says that representatives of `π` and `π'` exist
  with the twist of the first by `χ ∘ det` equivalent to the second.
- `IsSmoothDual F π π'` says the same for the smooth contragredient, which is
  the subspace of smooth vectors in the full algebraic dual, with the action
  through the group inverse.
- `IsRankOneCharacter F χ π` says that a representative of a rank-one class is
  equivalent to the one-dimensional representation `χ ∘ det` of `GL_1(F)`.
  Using the determinant avoids identifying `GL_1(F)` with `Fˣ` by fiat.

Each relation is a proposition on classes that quantifies over
representatives in the given classes, so no representative is chosen. They
are relations rather than functions, so they do not assume that the class
space is closed under the operation. In particular, the definitions do not
assume that the smooth contragredient of an irreducible admissible
representation is irreducible admissible. Existence and uniqueness of an
output are separate results. When the correspondence uses these relations,
the existence of an output is asserted explicitly in its statements.

`isCharacterTwist_iff_eq_twist` connects the twist relation with the
published class map `SmoothDualClass.twist` from
`Langlands.Representation.Category.Twist`. It applies when the kernel of
`χ ∘ det` is open: then `IsCharacterTwist F χ π π'` holds exactly when `π'`
is the image of `π` under that map. So in that case the relation has exactly
one output, and it agrees with the published adapter. The open-kernel
hypothesis is the published adapter's own hypothesis; this module does not
prove that it holds for every continuous `χ`.

## Sources and provenance

Henniart 2000 states its conventions for supercuspidal classes only. Section
1.1, printed page 439, introduces the set `A_F^0(n)` of isomorphism classes
of smooth irreducible supercuspidal representations of `GL_n(F)`; its
footnote 1 defines a quasi-character as a continuous homomorphism to `ℂˣ`,
with no unitarity condition. Section 1.2(1)–(3), printed page 440, states
the compatibilities of the supercuspidal correspondence with the central
quasi-character, with the twist by `χ ∘ det` and with contragredients.
Section 1.3, printed page 440, states that in rank one the correspondence is
given by local class field theory.

The full class space used here is the set `A(n)` of Henniart 2002, section
1.1, printed page 588: the isomorphism classes of smooth irreducible
representations of `GL_n(F)`, as distinguished there from the supercuspidal
subset `A^0(n)`. The remark in section 1.2, printed page 589, forms the
contragredient `π^∨ ∈ A(n)` of a class `π ∈ A(n)`. Section 2.5, printed page
595, defines the twist `χπ` as the class of `g ↦ χ(det g)π(g)`. Henniart
states `A(n)` for smooth irreducible representations, while the Lean class
space uses the published irreducible admissible category. The two agree by
the standard theorem that irreducible smooth representations of `GL_n(F)`
are admissible; this module neither proves nor uses that theorem.

The predicates are direct relational formulations of these operations, and
the existence assertions are deliberately kept separate. No special-quotient
or classification result of Henniart 2002, sections 2.6–2.9, is asserted.

- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

The implementation reuses published Library constructions without copying
them: `Langlands.Group.GL.Padic` (the canonical group topology),
`Langlands.Representation.Category.Basic` (`IrreducibleAdmissibleRep`,
`SmoothDualClass`), `Langlands.Representation.Twist.Definitions` (the twist),
`Langlands.Representation.Smooth.Contragredient.Definitions` (the smooth
contragredient), `Langlands.Representation.Category.Twist`
(`SmoothDualClass.twist`) and this task's `Langlands.Correspondence.LocalConventions`
(the quasi-character type).

## Validation

The module compiles in the project Lean service without errors or warnings.
The earlier development inspection printed the elaborated declarations with
universe parameters. `AutomorphicObject` and `AutomorphicClass` have sort
`Type (max uF (uV + 1))`. The four relations return `Prop` and have no
hypotheses beyond the field, the rank, the characters and the classes. The
rank-one equivalence compares a carrier in universe zero with one in universe
`uV`.
