# Irreducible affine roots from an irreducible relative root system

Module `Langlands.Geometry.Building.RelativeIrreducibleAffineRoots`.

## Contents

The module defines irreducibility of the relative root system of a split torus and transfers it
to an affine root system on an apartment whose derivative roots are the relative roots. It
connects the published Borel–Tits statement `RelativeRootSystemIrreducibleStatement` (module
`Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleStatement`) with the affine
irreducibility predicate `IsIrreducibleRoots` (KP Definition 1.3.13, module
`Langlands.Geometry.Building.AffineIrreducibleSimpleRoots`).

### Definition (namespace `Langlands.GroupScheme`)

Let `k` be a field, `G` an affine group scheme over `k` (`[IsAffineHom G.X.hom]`) and
`i : T.toGrp ⟶ G` a homomorphism from a commutative group scheme `T`. The Library supplies the
relative roots `relativeRoots i` (a set of characters of `T`), their rational span
`relativeRootSpan i` (a `ℚ`-subspace of `ℚ ⊗ X*(T)`) and the map `toRat` sending a character
`α` to `1 ⊗ α`.

- `IsIrreducibleRelativeRootSystem i : Prop` holds when, for every type `J : Type u` and every
  root pairing
  `P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))`
  whose pairing is evaluation (`P.toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i)`) and
  whose roots are exactly the elements `1 ⊗ α` for the relative roots `α`
  (`Subtype.val '' Set.range P.root = toRat '' relativeRoots i`), `P` is irreducible in Mathlib's
  sense `RootPairing.IsIrreducible`.

  Nothing is assumed about reducedness, crystallographic integrality or finiteness of `J`. No
  pairing is chosen: the predicate quantifies over all such pairings, and holds vacuously if
  there is none. The quantified condition is literally the conclusion of
  `RelativeRootSystemIrreducibleStatement`.

- `isIrreducibleRelativeRootSystem_of_isAlmostSimple hirr hG hi hne`: given
  `hirr : RelativeRootSystemIrreducibleStatement.{u}`, `hG : IsAlmostSimple G`,
  `hi : IsMaximalSplitTorus i` and `hne : (relativeRoots i).Nonempty`, one has
  `IsIrreducibleRelativeRootSystem i`. The statement is an explicit hypothesis; it is not proved
  in the Library (its proof is a separate task).

### Affine root systems (namespace `Langlands.Geometry.Building`)

Here `S` is a commutative group scheme over `k`, `i : S.toGrp ⟶ G`, `A` is an affine space
(any universe `uA`) under the real translation space `TranslationSpace i`, and
`Ψ : Set (A →ᵃ[ℝ] ℝ)` is an affine root system with `hΨ : IsAffineRootSystemWithRankZero Ψ`
(the Library form of KP axioms AR 1–AR 4). The hypothesis
`hderiv : derivativeRoots Ψ = Set.range (rootForm i)` says that the derivatives of the affine
roots are exactly the real linear forms `rootForm i α` of the relative roots `α`. No reducedness
of the relative roots is assumed.

- `relativeRoots_nonempty_of_derivativeRoots_eq hderiv hne`: if `Ψ` is nonempty then `i` has a
  relative root.
- `IsIrreducibleRelativeRootSystem.nonempty_and_isIrreducibleRoots h hS hΨ hderiv`: for
  `h : IsIrreducibleRelativeRootSystem i` and `hS : IsSplitTorus S.toGrp`,
  `Ψ.Nonempty ∧ IsIrreducibleRoots Ψ`.
- `IsIrreducibleRelativeRootSystem.isIrreducible_derivativePairing h hS hΨ hderiv`: under the
  same hypotheses, the finite real root pairing of derivative roots `hΨ.derivativePairing` is
  irreducible (`RootPairing.IsIrreducible`).
- `nonempty_and_isIrreducibleRoots_of_isAlmostSimple hstmt hG hi hne hΨ hderiv`: with
  `hstmt : RelativeRootSystemIrreducibleStatement.{u}`, `hG : IsAlmostSimple G`,
  `hi : IsMaximalSplitTorus i` and `hne : (relativeRoots i).Nonempty`,
  `Ψ.Nonempty ∧ IsIrreducibleRoots Ψ`.
- `isIrreducibleRoots_of_isAlmostSimple hstmt hG hi hΨ hderiv hne`: the same with
  `hne : Ψ.Nonempty` in place of a relative root; the conclusion is `IsIrreducibleRoots Ψ`.

The last two results take the Borel–Tits statement as an explicit hypothesis `hstmt`. They do not
construct the apartment or prove `hderiv`; a user supplies an affine root system whose derivative
roots are the relative roots.

## Provenance

- The predicate `IsIrreducibleRelativeRootSystem` names the conclusion of
  `RelativeRootSystemIrreducibleStatement`, which formalizes Borel–Tits, *Groupes réductifs*,
  Publ. Math. IHÉS 27 (1965), Corollaire 5.11 (printed p. 99, PDF p. 46): the relative root
  system `kΦ` of a group that is almost simple over `k`, with respect to a maximal `k`-split
  torus, is irreducible. As explained in the statement module, Mathlib's
  `RootPairing.IsIrreducible` formalizes Bourbaki's irreducibility used there, and the Library
  statement assumes a relative root (an anisotropic group has none).
- `IsIrreducibleRoots` is the formalization of Kaletha–Prasad, *Bruhat–Tits Theory: A New
  Approach* (2023), Definition 1.3.13 (printed p. 18, PDF p. 49).
- The theorems are internal: they derive affine irreducibility from relative irreducibility.
  They are the step in the proof of KP Theorem 10.3.1 (printed p. 392, PDF p. 423) where the
  affine root system of an apartment of an absolutely almost-simple group is used as an
  irreducible affine root system; they transcribe no new statement from the literature.

## Proof notes

- `relativeRoots_nonempty_of_derivativeRoots_eq`: a `ψ ∈ Ψ` has derivative `ψ̇` in
  `derivativeRoots Ψ = Set.range (rootForm i)`, and `rootForm i` is indexed by the relative
  roots.
- `nonempty_and_isIrreducibleRoots`: the published module `RelativeDerivativeRootPairing` gives
  the rational root pairing `relativeDerivativePairing i hS hΨ hderiv`, indexed by
  `derivativeRoots Ψ`, on `relativeRootSpan i` with evaluation pairing
  (`relativeDerivativePairing_toLinearMap`) and root image `toRat '' relativeRoots i`
  (`relativeDerivativePairing_root_image`). So `h` makes it irreducible. Its pairing equals that
  of `hΨ.rationalDerivativePairing` (`relativeDerivativePairing_pairing`), whose image in `ℝ` is
  `a(hΨ.derivativeCoroot b)` (`rationalDerivativePairing_pairing`); since `ℚ → ℝ` is injective,
  the zero patterns agree. The transfer lemma
  `IsAffineRootSystemWithRankZero.isIrreducible_iff_isIrreducibleRoots_of_equiv` (module
  `AffineIrreducibleDerivativeRoots`) with the identity bijection then gives
  `Ψ.Nonempty ∧ IsIrreducibleRoots Ψ`.
- `isIrreducible_derivativePairing` follows by `isIrreducible_iff_isIrreducibleRoots`.
- The almost-simple corollaries apply the statement through
  `isIrreducibleRelativeRootSystem_of_isAlmostSimple`, using that a maximal split torus is a split
  torus (`hi.isSplitSubtorus.1`), and for the last one obtain a relative root from `Ψ.Nonempty`.
