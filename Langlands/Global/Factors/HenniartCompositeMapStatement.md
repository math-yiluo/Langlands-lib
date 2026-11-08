# Henniart's composite map at a p-adic field

This file contains derived **statement targets**. It has no proof of the three
targets, which are:

- `Langlands.Global.PoleComparison.HenniartCompositeOperationStatement`, with level
  parameters `uF uK uW uP`;
- `Langlands.Global.PoleComparison.HenniartCompositeFactorStatement`, with level
  parameters `uF uK uW uP uE`;
- `Langlands.Global.PoleComparison.HenniartCompositeMapStatement`, with level
  parameters `uF uK uW uP uE`.

They form unit U4b of the H3 program (Henniart's global construction, task
`34b81620-20d7-4059-9b08-6bedd1c1c029`). The targets are derived analogues of
Henniart's §3.7 composite map, written `R_E(F) → R_A(F)` in his local notation
(see "Notation" below), and of its properties in §3.8 (a)–(c). They are stated for the finite-relative, witnessed objects that the
published U4a statements use. The first two targets are pure transport of
structure along an isomorphism of p-adic fields `K ≅ F_v`, and they have no deep
hypothesis. The third combines them with the published U4a statements
`RelativeIsometryOperationStatement` and `RelativeIsometryFactorStatement`. The
module also defines the K-side predicates, the transports along `K ≅ F_v` and the
composite map. It proves three small API theorems.

## Setting

Two kinds of object appear.

- **A p-adic field `K`.** `K : PadicField.{uK} p` for a prime `p`. The predicates
  in the namespace `Langlands.Correspondence.LatticeMap` concern a `ℤ`-linear
  equivalence `Φ : W ≃ₗ[ℤ] A`. Here `W` is a submodule of the unitary Weil lattice
  `LocalWeil.UnitaryLattice K`, and `A` is a submodule of the unitary
  supercuspidal lattice `PadicSupercuspidal.UnitaryLattice K`. These predicates
  use only objects attached to `K`: its own reciprocity candidates, characters,
  additive characters, measures and local-constant systems.
- **The global data of the published U4a statements.** These are number fields
  `F` and `E` in a common universe `uF` with `E/F` Galois, the compact adele
  quotient instance, a fundamental class family `c`, a finite place `v` of `F`,
  and a linear equivalence
  `T : weilImage F E c v ≃ₗ[ℤ] automorphicImage F E c v` between the published
  witnessed relative images at `v`. These images sit in the unitary lattices of
  `padicField v`. Further data are `h : residuePrime v = p` and a `ℚ_p`-algebra
  isomorphism `f : K ≅ (padicFieldAt v h)`. The `ℚ_p`-algebra structure on the
  target is `(padicFieldAt v h).algebra`. This is exactly the form of `f` in the
  published `HenniartGlobalizationStatement` (U2).

## Helper declarations

In the namespace `Langlands.Global`:

- `padicFieldAtSupercuspidalLatticeEquiv v h` identifies the unitary
  supercuspidal lattices of `padicField v` and of `padicFieldAt v h`. After
  `subst h` it is the identity. It is the supercuspidal analogue of the
  published `padicFieldAtWeilEquiv`.
- `completionWeilEquiv v h K f : W_K ≃ₜ* W_{F_v}` is `extensionWeilEquiv` for
  `f.symm` (U4b M1, `Langlands/Weil/Local/ExtensionWeilEquiv.lean`), followed by
  `padicFieldAtWeilEquiv v h`.
- `coe_completionWeilEquiv` is a proved theorem (`rfl`). As a continuous
  homomorphism, `completionWeilEquiv` is the published
  `completionWeilTransport v h K f` of U2.
- `completionWeilLatticeEquiv v h K f` is the pullback of unitary Weil classes from
  `F_v` to `K` along `completionWeilEquiv`. It is
  `Weil.restrictUnitaryLatticeEquiv` (U4b M2,
  `Langlands/VirtualRepresentation/Weil/GroupTransport.lean`).
- `continuousRestrict_completionWeilTransport_eq_iff` is a proved theorem. It
  says the comparison in U2's conclusion holds exactly when
  `completionWeilLatticeEquiv v h K f y = x`. The comparison is restriction along
  `completionWeilTransport` in the exact Grothendieck group of `W_K`. The proof
  rewrites with `coe_completionWeilEquiv` and applies the M2 theorem
  `Weil.continuousRestrict_realizeExact_includeUnitary_eq_iff`. So every `x` that
  U2 produces from some `y` in `weilImage F E c v` lies in the domain of the
  composite map below.
- `completionSupercuspidalLatticeEquiv v h K f` is the pullback of unitary
  supercuspidal classes from `F_v` to `K` along `f`. It is
  `padicFieldAtSupercuspidalLatticeEquiv` followed by
  `PadicSupercuspidal.unitaryLatticeEquiv K (padicFieldAt v h) f` (U4b M3,
  `Langlands/VirtualRepresentation/Supercuspidal/FieldTransport.lean`).

In the namespace `Langlands.Global.PoleComparison`:

- `henniartCompositeMap F E c v h K f T` goes from the image of `weilImage F E c v`
  under `completionWeilLatticeEquiv` to the image of `automorphicImage F E c v`
  under `completionSupercuspidalLatticeEquiv`. It pulls a class back to `F_v`,
  applies `T`, and pulls the result back to `K`. It is a linear equivalence, so
  it is injective by construction, as Henniart remarks at the start of §3.8.
- `henniartCompositeMap_apply` is a proved theorem. On the transport of `x` in
  `weilImage`, the composite map is the transport of `T x`.

## The predicates at `K`

For `Φ : W ≃ₗ[ℤ] A` as in the setting:

- `LatticeMap.Isometry K Φ`: `Φ` preserves the integral multiplicity pairings and
  the degrees.
- `LatticeMap.GeneratorCompatibility K Φ`: for every `x` in `W`, `x` is a basis
  vector `generator b` with `b` in `LocalWeil.UnitaryBasis K` exactly when `Φ x`
  is a basis vector `generator b'` with `b'` in `PadicSupercuspidal.UnitaryBasis K`.
  The first basis consists of the irreducible unitary Weil classes. The second
  consists of the unitary supercuspidal classes.
- `LatticeMap.DualCompatibility K Φ`: `W` is closed under
  `LocalWeil.unitaryDualLatticeEquiv`. `Φ` sends the contragredient of `x` to the
  actual smooth contragredient `PadicSupercuspidal.unitaryContragredientLatticeEquiv`
  of `Φ x`.
- `LatticeMap.TwistCompatibility K Φ e χ hχ`: `W` is closed under
  `LocalWeil.unitaryFieldCharacterTwistLatticeEquiv K e χ hχ`, the twist by
  `weilCharacter e χ`. `Φ` sends the twist of `x` to
  `PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv K χ hχ (Φ x)`, the twist
  by `χ ∘ det`. Both twist equivalences are published in U4a-ii.
- `LatticeMap.CharacterCompatibility K Φ e χ`: some `x` in `W` includes to the
  basis vector of `Correspondence.rankOneWeilCharacterClass K e χ`. Its image
  `Φ x` includes to the basis vector of
  `Correspondence.rankOneSupercuspidalClass K χ`, the `GL_1` class of `χ`.
- `LatticeMap.DeterminantCompatibility K Φ e`: for every `x` in `W` there is
  `ω : K^× →* ℂ^×` such that `ω` is a central character of `Φ x`
  (`PadicSupercuspidal.IsUnitaryCentralCharacter`, published in U4a-i), and
  `ω (reciprocityHom K e w) = det x (w)` for every `w` in `W_K`. The virtual
  determinant is `LocalWeil.unitaryDeterminant` (U4a-i).
- `LatticeMap.PairFactorCompatibility K Φ ψ`: there is a measure `ν` that is
  self-dual for `ψ`. For every such `ν`, every `x, y` in `W` satisfy two
  conditions. First, `PadicSupercuspidal.IsUnitaryPairLFactor K ψ ν (Φ x) (Φ y)`
  holds for the rational function `LocalWeil.unitaryPairLFactor K x y`. Second,
  for every local-constant system `(eC, ε, hε)` of `K`, some `(c, m)` is both
  `LocalWeil.IsUnitaryPairEpsilonFactor K eC ε hε ψ x y` and
  `PadicSupercuspidal.IsUnitaryPairEpsilonFactor K ψ ν (Φ x) (Φ y)`. All these
  virtual factor relations are published in U4a-i.
- `LatticeMap.OperationProperties K Φ` bundles `Isometry`,
  `GeneratorCompatibility` and `DualCompatibility`. It also requires
  `TwistCompatibility` and `CharacterCompatibility` for every candidate `e` with
  `Correspondence.IsGeometricReciprocity K e` and every modulus-one `χ`.
- `LatticeMap.FactorProperties K Φ` requires `DeterminantCompatibility` for every
  geometric candidate `e` and `PairFactorCompatibility` for every nontrivial
  additive character `ψ` of `K`.
- `LatticeMap.HenniartProperties K Φ` is the conjunction of the two bundles.

The K-side predicates are the U4a-ii and U4a-i predicates
(`RelativeIsometryOperations`, `RelativeIsometryFactors`), together with the
pairing, degree and generator clauses of `RelativeGeneratedPositiveIsometry`. Two
things change. The base field `padicField v` becomes an arbitrary `K`, and the
fixed images become arbitrary submodules `W` and `A`.

## The targets

- `HenniartCompositeOperationStatement`: assume `T` satisfies
  `RelativeGeneratedPositiveIsometry F E c v T` and
  `RelativeIsometryOperations F E c v T`. Then for every `p`, `h`, `K` and `f`,
  the composite `henniartCompositeMap F E c v h K f T` satisfies
  `LatticeMap.OperationProperties K`.
- `HenniartCompositeFactorStatement`: assume `T` satisfies
  `RelativeIsometryFactors F E c v T`. Then for every `p`, `h`, `K` and `f`, the
  composite satisfies `LatticeMap.FactorProperties K`.
- `HenniartCompositeMapStatement` (Henniart 3.8): assume
  `RelativeWeilGroup.IsArithmeticClassFamily c`, a nontrivial additive character
  `ψ` of `F_v` with `RelativeCertifiedPoleComparisons F E c v ψ`, and `T` with
  `RelativeGeneratedPositiveIsometry`. Then for every `p`, `h`, `K` and `f`, the
  composite satisfies `LatticeMap.HenniartProperties K`. The hypotheses are
  those of the published `RelativeIsometryOperationStatement` and
  `RelativeIsometryFactorStatement`. The published theorem `relativePolePairing`
  gives exactly one such `T` under the pole hypothesis, so the target is not
  vacuous.

## Conventions and adaptations

- **Notation.** In Henniart's §3 the p-adic field is `F`, and `E/F` is a finite
  Galois extension of p-adic fields. The number field is a bold `𝐅` with a place
  `0`, and `φ_0` identifies `F` with the completion `𝐅_0`. In this file `F` and
  `E` are number fields. Below, Henniart's local `F` is written `K`, his local
  `E` is written `K_E`, and his `R_E(F)` is written `R_{K_E}(K)`.
- **K-intrinsic conventions.** The conclusions quantify over all geometric
  reciprocity candidates, modulus-one characters, nontrivial additive
  characters, self-dual measures and local-constant systems of `K` itself. None
  of them is transported from `F_v`. Henniart (§3.8, printed p.451) likewise
  uses the reciprocity map, characters and additive character of the p-adic
  field itself. By local class field theory there is exactly
  one geometric candidate. In the Library this is the published, still unproved
  `LocalClassField.WeilReciprocityExistenceUniqueness`, so the targets fix no
  candidate. The reciprocity, unitarity and ε-system conventions are those of
  U4a-i and U4a-ii, as explained in their Markdown files.
- **Domain of the map.** Henniart's composite has domain `R_{K_E}(K)`, the
  classes that factor through `Gal(K_E/K)`. He embeds `R_{K_E}(K)` into the
  subgroup `R_0` of `R_G(K)` that corresponds to `R_G(𝐅, 0)` via `φ_0`. The
  embedding uses Brauer's theorem and the constructions of §§3.4–3.6. Here the
  domain is the
  whole transported Weil image, the analogue of `R_0`. The embedding of a given
  class of `W_K` is a separate question. U2 (`HenniartGlobalizationStatement`)
  answers it for classes that factor through a finite quotient, through
  `continuousRestrict_completionWeilTransport_eq_iff`.
- **Twists.** Henniart's twist clause in 3.8 (a) is restricted to characters of
  `K^×` trivial on `N_{K_E/K}(K_E^×)`, so that the twisted class stays in
  `R_{K_E}(K)`.
  The transported Weil image comes from the relative Weil group at level `E/F`.
  U4a-ii states closure of the Weil image under twists by every modulus-one
  character. The transport therefore keeps that form, and no norm condition
  appears.
- **Characters.** Henniart's (c) says `π(ρ)` is given by class field theory if
  `ρ` is a character in `R_{K_E}(K)`. `CharacterCompatibility` also states that the
  rank-one class lies in `W`, as in U4a-ii.
- **Generators.** Henniart's (c) says `ρ` is irreducible exactly when `π(ρ)` is
  supercuspidal. In the lattices, the irreducible unitary classes are exactly the
  basis vectors.
- **Universes.** `K` is in universe `uK`, and the number fields are in `uF`. The
  supercuspidal side at `K` keeps the form-space universe `uF` of
  `automorphicImage`. Weil carriers use `uW`, presentation factors `uP`, and
  local-constant systems the representation universe `uE`. Hence
  `FactorProperties` and `HenniartProperties` appear at levels `{uK, uW, uF, uE}`.
  To combine with U2, whose number fields lie in `Type`, instantiate `uF := 0`.

## Relation to Henniart's absolute-global objects

Henniart's `R_G(𝐅, 0)` and `R_A(𝐅, 0)` (§2.5, printed pp.445–446) are spanned by
the local data of all associated pairs for the absolute global Weil group. The
published `weilImage` and `automorphicImage` are instead spanned by the witnessed
generators at one finite Galois extension `E/F`. As the U4a Markdown files and
the imported `RelativeImages` Markdown record, comparison with the absolute
objects is a separate obligation. These targets leave it open. The composite map
is not identified with Henniart's map. Henniart's map is examined for
independence of the global choices in §4, which is outside this unit.

## Why the targets are true

Henniart's argument for 3.8 is "par transport de structure, grâce à 2.6"
(printed p.451). The targets split it into a transport part and an assembly part.
Everything below is a future proof obligation.

Write `L = completionWeilLatticeEquiv v h K f`,
`S = completionSupercuspidalLatticeEquiv v h K f` and
`φ = completionWeilEquiv v h K f`. By `henniartCompositeMap_apply`, the composite
sends `L y` to `S (T y)`. Each K-side clause for `L y` thus reduces to the
corresponding `F_v` clause for `y`, once `L` and `S` are known to commute with
the relevant structure. Here `F_v` means `padicField v`, identified with
`padicFieldAt v h` after `subst h`.

- **Pairing, degree and generators.** `L` and `S` map basis vectors to basis
  vectors bijectively, by `Weil.restrictUnitaryBasisEquiv` and
  `PadicSupercuspidal.unitaryBasisEquiv`. So `L` and `S` preserve the orthonormal
  pairings. Restriction along an isomorphism preserves dimension, and the field
  pullback preserves the rank, so they also preserve degrees. For `L` these are
  the M2 theorems `Weil.unitaryPairing_restrictUnitaryLatticeEquiv` and
  `Weil.unitaryDegree_restrictUnitaryLatticeEquiv`. At `F_v`, the forward
  direction of the generator clause follows from the last clause of
  `RelativeGeneratedPositiveIsometry`, because a basis vector has self-pairing one
  and positive degree. For the converse, suppose `T y` is a basis vector. By the
  isometry clauses, `y` has self-pairing one and positive degree. An element of
  an orthonormal integral lattice with self-pairing one is plus or minus a basis
  vector, and positive degree fixes the sign.
- **Contragredients.** Restriction along `φ` commutes with the contragredient,
  and the field pullback commutes with the smooth contragredient. Then the dual
  clause of U4a-ii at `y` gives the K-side dual clause at `L y`.
- **Twists and characters.** Let `e` be a geometric candidate of `K` and `χ` a
  modulus-one character of `K^×`. Transport `e` to the candidate `e'` of `F_v`
  determined by `reciprocityUnits e' (φ w) = f (reciprocityUnits e w)`. Choose
  an isomorphism of algebraic closures extending `f`; it exists by uniqueness of
  algebraic closures, and it induces `φ`. It carries the geometric relation for
  `e` to the one for `e'`. Put `χ' = χ ∘ f⁻¹`, again of modulus one. Then
  `weilCharacter e' χ' ∘ φ = weilCharacter e χ`, so `L` carries the twist by
  `(e', χ')` to the twist by `(e, χ)` and the rank-one class of `(e', χ')` to the
  rank-one class of `(e, χ)`. Since `det` commutes with `GL_n(f)`, `S` carries the
  twist by `χ' ∘ det` to the twist by `χ ∘ det` and the `GL_1` class of `χ'` to
  that of `χ`. The twist and character clauses of U4a-ii at `(e', χ')` then give
  the K-side clauses at `(e, χ)`.
- **Determinants.** With `e'` as above, `det (L y) = det y ∘ φ`. If `ω'` is a
  central character of `T y`, then `ω' ∘ f` is a central character of `S (T y)`,
  and `ω' (f (rec_e w)) = ω' (rec_e' (φ w)) = det y (φ w)`.
- **Pair factors.** Put `ψ' = ψ ∘ f⁻¹`, again nontrivial. A measure `ν` on `K` is
  self-dual for `ψ` exactly when its pushforward `ν'` along `f` is self-dual for
  `ψ'`. Both fields have the same residue cardinality, so the variable
  `q^(-s)` is the same. Transport along `f` matches Whittaker models and the JPSS
  integrals. Hence the JPSS L-polynomial and ε relations for the pullbacks along
  `f` at `(ψ, ν)` are the relations at `(ψ', ν')`. On the Weil side, `φ` comes
  from an isomorphism of algebraic closures, so it carries inertia to inertia and
  Frobenius cosets to Frobenius cosets. The arithmetic pair L-factors are
  therefore invariant under `L`. Next, extend `f` to an isomorphism of the
  specified common closures. It carries finite intermediate fields, Weil groups,
  additive characters, Haar measures and exact virtual classes. Through it, a
  local-constant system `(eC, ε, hε)` of `K` transports to a system of `F_v`, and
  the arithmetic pair ε-certificates correspond. The pair-factor clause of U4a-i
  at `ψ'` then gives the K-side clause at `ψ`. The self-dual measure required at
  `K` is the transport of the one required at `F_v`.
- **Assembly (3.8).** Under the hypotheses of `HenniartCompositeMapStatement`, the
  published `RelativeIsometryOperationStatement` gives
  `RelativeIsometryOperations`. Its proof task is `c7b60e52`. The published
  `RelativeIsometryFactorStatement` gives `RelativeIsometryFactors`. Its proof
  task is `aa6b0765`. The two transport targets then give the two bundles.

## Provenance

The source is Henniart, *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455:

- §3.7, the composite map `R_E(F) → R_A(F)` in his local notation, printed
  p.451;
- §3.8 (a)–(c), the properties of the composite map, obtained by transport of
  structure from Proposition 2.6, printed p.451;
- Proposition 2.6, printed pp.446–447, and §2.5, printed pp.445–446.

Printed page `p` is page `p - 438` of the PDF, counting from 1. The Lean
formulation is derived. The transported witnessed images play the roles of
Henniart's `R_0` and its image in `R_A(F)`. The composite of the transports with
the `T` of `RelativeGeneratedPositiveIsometry` plays the role of his map
`ρ ↦ π(ρ)`, but it is not identified with it.
