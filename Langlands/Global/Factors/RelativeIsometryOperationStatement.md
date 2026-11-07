# Contragredient, twist and character compatibility of the relative isometry

This is a derived **statement target**. The file contains no proof of
`Langlands.Global.PoleComparison.RelativeIsometryOperationStatement`, whose
level parameters are `uF uW uP`. It is unit U4a-i of the H3 program
(Henniart's global construction, task
`34b81620-20d7-4059-9b08-6bedd1c1c029`). Worker 30, whose task `62ea68fa`
lists the same sections of Henniart as source leads, agreed that H3 states
it. The target is a derived analogue, at a fixed finite relative level `E/F`
and for witnessed spans, of the contragredient and twist clauses of
Henniart's Proposition 2.6 (a) and of all of Proposition 2.6 (c). Henniart
states these clauses for the images of the absolute global Weil group. The
target does not identify its spans or its isometry with those absolute-global
objects (see "Relation to Henniart's absolute-global objects" below). The
analogues of the degree clause of (a) and of the scalar-product clause of (b)
are already part of the published `RelativeGeneratedPositiveIsometry`. The
determinant clause of (a) and the L- and ε-factor clauses of (b) are not
stated here.

## Setting

The objects are those of the published
`RelativePolePairingStatement` (`Langlands/Global/Factors/RelativePolePairingStatement.lean`):

- number fields `F` and `E` in a common universe, with `E/F` Galois;
- the compact adele quotient instance;
- a fundamental class family `c` with `RelativeWeilGroup.IsArithmeticClassFamily c`;
- a finite place `v` of `F` and a nontrivial additive character `ψ` of `F_v`.

The pole-comparison input `RelativeCertifiedPoleComparisons F E c v ψ` is kept
as an explicit hypothesis. `weilImage F E c v` and `automorphicImage F E c v`
are the published integral spans of the local elements of all witnessed
generators (`RelativeGlobal.WitnessedGenerator`). They sit in the unitary
Weil lattice `LocalWeil.UnitaryLattice (padicField v)` and in the unitary
supercuspidal lattice `PadicSupercuspidal.UnitaryLattice (padicField v)`.
The statement concerns every linear equivalence
`T : weilImage ≃ₗ[ℤ] automorphicImage` satisfying
`RelativeGeneratedPositiveIsometry`. Under the pole hypothesis the published
theorem `relativePolePairing` gives exactly one such `T`, so the statement is
not vacuous. This `T` is the relative, witnessed analogue of Henniart's
isomorphism `ρ ↦ π(ρ)` of Theorem 2.5; it is not identified with that
isomorphism. All conclusions are restricted to the generated spans at the
fixed level `E/F`. Nothing is claimed about the full local lattices.

## Helper declarations

- `PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv F χ hχ` twists the
  unitary supercuspidal lattice by `χ ∘ det` in every rank. Here `χ` is a
  continuous character of `F^×` (`Correspondence.QuasiCharacter F`) and `hχ`
  says `|χ(a)| = 1` for every `a`. It is the published
  `Supercuspidal.unitaryTwistLatticeEquiv` for the family
  `n ↦ Correspondence.determinantQuasiCharacter F n χ`. The published
  `isOpen_ker_determinantQuasiCharacter` and
  `GeneralLinear.ker_determinant_le_ker_comp` supply the kernel conditions.
- `LocalWeil.norm_weilCharacter_eq_one` is a proved theorem: the pullback
  `LocalFactor.RankOne.weilCharacter F e χ` of a modulus-one field character
  along a reciprocity candidate `e` also has modulus one. The proof is
  `hχ _`, since the pullback is `χ` composed with `reciprocityUnits F e`.
- `LocalWeil.unitaryFieldCharacterTwistLatticeEquiv F e χ hχ` is the published
  `LocalWeil.unitaryTwistLatticeEquiv` for that pulled-back Weil character.

## The predicates

For a fixed `T`:

- `RelativeIsometryDualCompatibility`: for every `x` in `weilImage`, the
  contragredient `LocalWeil.unitaryDualLatticeEquiv x` lies in `weilImage`, and
  `T` sends it to `PadicSupercuspidal.unitaryContragredientLatticeEquiv (T x)`.
  This is the actual smooth contragredient on supercuspidal classes. It is
  the relative analogue of Henniart's `π(ρ^∨) = π(ρ)^∨`, together with
  stability of the span under duals, which Henniart uses implicitly for
  `R_G(F, 0)`.
- `RelativeIsometryTwistCompatibility e χ hχ`: for every `x` in `weilImage`, the
  twist of `x` by `weilCharacter e χ` lies in `weilImage`, and `T` sends it to
  the twist of `T x` by `χ ∘ det`. It is the relative analogue of Henniart's
  `π((χ ∘ τ_{F_0}) ⊗ ρ) = (χ ∘ det) π(ρ)`.
- `RelativeIsometryCharacterCompatibility e χ`: some `x` in `weilImage`
  includes, through `LocalWeil.includeUnitary`, to the basis vector
  `generator ⟨1, Correspondence.rankOneWeilCharacterClass e χ⟩`. This is the
  rank-one class of `weilCharacter e χ`. Moreover, `T x` includes, through
  `PadicSupercuspidal.includeUnitary`, to the basis vector
  `generator ⟨1, Correspondence.rankOneSupercuspidalClass χ⟩`, the `GL_1`
  class of `χ`. It is the relative analogue of Henniart's (c): a unitary
  character of `W_{F_0}` lies in `R_G(F, 0)`, and `π` sends it to the
  character of `F_0^×` given by class field theory.
- `RelativeIsometryOperations T` is the dual clause, together with the twist
  and character clauses for every candidate `e` satisfying
  `Correspondence.IsGeometricReciprocity` and every modulus-one `χ`.

`RelativeIsometryOperationStatement` says: for all `F, E, c, v, ψ` as above,
`IsArithmeticClassFamily c` and the certified pole comparisons at `v` and `ψ`
imply `RelativeIsometryOperations T` for every `T` satisfying
`RelativeGeneratedPositiveIsometry`.

## Conventions and adaptations

- **Reciprocity.** Henniart (§1.1, printed p.439) normalizes local reciprocity
  so that geometric Frobenius elements correspond to uniformizers. The target
  uses the published geometric relation `IsGeometricReciprocity` and
  quantifies over every candidate that satisfies it. By local class field
  theory there is exactly one such candidate. In the Library this existence
  and uniqueness is the published, still unproved statement
  `LocalClassField.WeilReciprocityExistenceUniqueness`, so the target fixes
  no candidate. Every unitary character of `W_{F_v}` is
  `weilCharacter e χ` for a unique modulus-one `χ`, via the published
  equivalence `weilCandidateCharacterEquiv`. Therefore (c) is stated with
  field characters.
- **Unitarity.** Henniart's footnote 1 (printed p.439) calls a continuous
  homomorphism to `ℂ^×` a quasicharacter, and a character if it is unitary.
  His Proposition 2.6 (a) is stated for every *caractère* of `F_0^×`, and his
  (c) for unitary characters of `W_{F_0}`. The modulus-one quantifier `hχ`
  therefore matches the source; it is not a narrowing. It is also what makes
  the twists act on the lattices spanned by unitary irreducible classes.
- **Additive character and measures.** `ψ` and the self-dual measures appear
  only in the retained hypothesis `RelativeCertifiedPoleComparisons`, exactly
  as in `RelativePolePairingStatement`.
- **Universes.** The level parameters are those of the published images:
  `uF` for the fields, `uW` for Weil carriers and `uP` for presentation
  factors. The supercuspidal side uses the form-space universe `uF`. The
  universe `uV` appears only in the helper equivalences.

## Relation to Henniart's absolute-global objects

Henniart (§2.1, printed p.444) works with the absolute global Weil group
`W_F`. His `R_G(F, 0)` and `R_A(F, 0)` (§2.5, printed pp.445–446) are spanned
by the local data of *all* associated pairs of an irreducible unitary
representation of `W_F` and a unitary cuspidal representation. The published
`weilImage` and `automorphicImage` are instead spanned by the local elements
of the witnessed generators at one finite Galois extension `E/F`: an
irreducible unitary representation of `RelativeWeilGroup c F E`, an actual
cuspidal realization with a presentation, weak association, a local relative
Weil map at a place above `v`, an exact local expansion and a unitary
supercuspidal support, all supplied as data. As the imported
`RelativeImages` Markdown records, the comparison between relative and
absolute images, global automorphic unitarity, and the existence and
uniqueness of local maps, expansions and supports are separate obligations.
This statement leaves all of them open. It asserts the operation clauses for
the relative spans only.

## Why the target is true

Henniart's proof in §2.8 (printed p.448) obtains these clauses from §2.2
(printed p.444). The sketch below carries it out at the same fixed level
`E/F`. It does not use the pole hypothesis: a `T` satisfying
`RelativeGeneratedPositiveIsometry` is fixed on the generators, so each clause
reduces by linearity to a statement about witnessed generators. The published
`relativePolePairing` proves only that such a `T` exists, is unique and
preserves degrees and pairings. Everything below is a future proof
obligation; the named statements are published but not yet proved.

- **Dual.** Let `d` be a witnessed generator with Weil representation `S` and
  cuspidal realization `Π`. A dual witnessed generator at the same `E/F` must
  be built. Its Weil part is `S^∨`, again an irreducible unitary
  representation of `RelativeWeilGroup c F E`. Its cuspidal part is a
  contragredient realization `Π^∨` with a presentation whose local components
  are irreducible and admissible, and whose component at `v` is the smooth
  contragredient (`Automorphic.CuspidalContragredientStatement`; its existence
  clause needs a unitary central character for `Π`). Weak association of `S^∨`
  with `Π^∨` is `RelativeWeilGroup.AssociatedContragredientStatement`
  (Henniart §2.2: Satake parameters are inverted). The same local relative
  Weil map is kept. Exact expansions dualize termwise, and the supercuspidal
  support of the contragredient of a representation induced from
  `σ_1 ⊗ … ⊗ σ_r` is `{σ_i^∨}`. This gives a witnessed generator whose Weil
  element is the dual of `d.weilElement` and whose automorphic element is the
  contragredient of `d.automorphicElement`.
- **Twist.** A modulus-one character `χ` of `F_v^×` extends to a unitary Hecke
  character `χ'` of `𝔸_F^×/F^×` (the remark at the end of Henniart §2.8):
  `χ'` composed with the inclusion `IdeleClassGroup.ofAdicCompletion` of
  `F_v^×` is `χ`. This holds because the image of `F_v^×` in the idele class
  group is closed and meets `F^×` trivially, and characters of closed
  subgroups of locally compact abelian groups extend. On the Weil side, the
  twisted generator uses `(reciprocityCharacter c F E χ') ⊗ S`. The published
  `RelativeWeilGroup.reciprocityCharacter c F E χ'` is
  `w ↦ χ'(transfer c F E w)⁻¹`. It plays the role of Henniart's `χ' ∘ τ_F`,
  where at finite level `τ_F` is the pointwise inverse of the published
  `RelativeWeilGroup.transfer`; the transfer itself is not `τ_F` (see the
  published `RelativeWeilTransfer.md`, "Frobenius"). On the cuspidal side the
  twisted generator uses the determinant multiple of `Π` by `χ'`. Their weak
  association, and that of every presentation, is the published
  `RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement`, the
  second conjunct of `HeckeDeterminantTwistStatement`. That conjunct concludes
  `IsWeaklyAssociated (FiniteRepresentation.twist (reciprocityCharacter c F E χ') S)
  P'.spectralSystem`. The first conjunct, `CuspidalDeterminantMultipleStatement`,
  supplies the determinant multiple. The local component at `v` twists by
  `χ ∘ det`, and supercuspidal supports twist termwise. The remaining
  obligation is the local identity at `v`, which needs two inversions. Let `ι`
  be the generator's local relative Weil map at `v`. The published
  `RelativeWeilGroup.LocalTransferReciprocityStatement` gives
  `HasLocalTransferReciprocity v ι`: for every geometric candidate `e` of
  `F_v` and every `g`,
  `transfer c F E (ι g) = (ofAdicCompletion v (reciprocityUnits e g))⁻¹`.
  Hence `reciprocityCharacter c F E χ' (ι g) = χ'(ofAdicCompletion v
  (reciprocityUnits e g)) = χ(reciprocityUnits e g) = weilCharacter e χ g`.
  So the twisted Weil representation restricts along `ι` to the twist of
  `S ∘ ι` by `weilCharacter e χ`, as the target requires. This step needs
  `IsArithmeticClassFamily c`, the specification `IsLocalRelativeWeilMap`
  and a proof of `LocalTransferReciprocityStatement`, which the Library does
  not yet have. It also needs existence of the geometric candidate
  (`LocalClassField.WeilReciprocityExistenceUniqueness`). The proof of the
  published `RelativePolePairingStatement` provides none of this: it gives
  only the unique isometry `T`.
- **Characters.** With `χ'` as above, the one-dimensional representation
  `reciprocityCharacter c F E χ'` of `RelativeWeilGroup c F E` and the `GL_1`
  cuspidal realization given by `χ'` must be shown weakly associated. At a
  finite place `z` where `χ'` is unramified, the same two inversions give
  `reciprocityCharacter c F E χ' (ι_z Fr_z) = χ'_z(ϖ_z)`, since a geometric
  candidate sends the geometric Frobenius `Fr_z` to a uniformizer `ϖ_z`
  (Tate 1979, (1.4.1), p.6). This is the Satake parameter of `χ'` at `z`, as
  in item 4 of the published `HeckeDeterminantTwistStatement.md`. A local
  relative Weil map at `v` with an exact expansion and the `GL_1` support must
  be supplied. By the local identity of the twist step, their local elements
  at `v` are the classes of `weilCharacter e χ` and of `χ`, so they form a
  witnessed generator of rank one at level `E/F`.

## Provenance

The source is Henniart, *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455:

- §2.6, Proposition, (a) and (c), printed pp.446–447;
- the proof in §2.8, printed p.448;
- the twist and dual properties of association in §2.2, printed p.444;
- the absolute global Weil group setting in §2.1, printed p.444, and the
  definition of `R_G(F, 0)` and `R_A(F, 0)` in §2.5, printed pp.445–446;
- the normalization of reciprocity in §1.1, printed p.439;

- footnote 1, printed p.439: characters are unitary quasicharacters.

Printed page `p` is page `p - 438` of the PDF, counting from 1. The Lean
formulation is derived: it is a finite-relative, witnessed analogue of the
selected clauses. The published `weilImage` and `automorphicImage` at level
`E/F` play the roles of Henniart's `R_G(F, 0)` and `R_A(F, 0)`, and the `T` of
`RelativeGeneratedPositiveIsometry` plays the role of his isomorphism, but
they are not identified with them. His local reciprocity map `τ_{F_0}`
corresponds to a candidate satisfying the geometric relation.
