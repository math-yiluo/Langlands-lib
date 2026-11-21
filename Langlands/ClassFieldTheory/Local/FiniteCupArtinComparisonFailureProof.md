# The arithmetic inverse-cup character comparison is false

`Langlands.ClassFieldTheory.Local.finiteCupArtinCharacterComparisonFails` proves the
statement `FiniteCupArtinCharacterComparisonFails.{u}`, that is
`¬ FiniteCupArtinCharacterComparison.{u}`, in every universe `u`. The statement is in
module `Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonFailureStatement`.

## Why the comparison is false

`FiniteCupArtinCharacterComparison` says that `arithmeticReciprocityOfCup`, evaluated by
every character `ψ : Gal(D/F) →* Multiplicative (ZMod [D : F])`, gives the carry value
`FiniteArtinSymbol.symbolValue ψ a`. The Library proves that `geometricReciprocityOfCup`
has these values: this is `finiteGeometricCupArtinCharacterComparison` (module
`Langlands.ClassFieldTheory.Local.FiniteGeometricCupArtinComparisonProof`), and it is the
true statement. By `geometricReciprocityOfCup_eq_inv`, the geometric reciprocity map is
the inverse of the arithmetic one. If both comparisons held, every such character value
would equal its own inverse. An unramified cubic extension has a character of order three,
which contradicts this.

The Library's finite Artin symbol `FiniteArtinSymbol.artinSymbol` follows the arithmetic
normalization: by `artinSymbol_eq_of_arithmeticCoordinate` it sends a uniformizer to
arithmetic Frobenius for an unramified extension with its arithmetic coordinate. The
proposition was written as if the map named `arithmeticReciprocityOfCup` had that
normalization too. Under the Library's sign for the degree minus two cup it has the
geometric one.

## Implemented proof

`FiniteCupArtinComparisonRefutation.character_sq_eq_one` assumes the arithmetic comparison
`H`. It fixes `F`, a finite Galois extension `D/F` in the same universe, a character `ψ`
into `ZMod [D : F]` and an element `g` of `Gal(D/F)`, and proves `ψ g ^ 2 = 1`.

1. Take the canonical positive fundamental class
   `FiniteArtinTransferReduction.fundamentalClass F D`, its certificate
   `fundamentalClass_spec` and its cup bijectivity `cup_bijective`.
2. The norm-quotient projection is surjective, so some unit `a` has norm class
   `abelianizationCupEquiv c h (of g)`. Hence arithmetic inverse cup sends that class to
   `of g`.
3. `H` gives `ψ g = ofAdd (symbolValue ψ a)`.
4. The published geometric comparison, rewritten by `geometricReciprocityOfCup_eq_inv` and
   `map_inv`, gives `(ψ g)⁻¹ = ofAdd (symbolValue ψ a)`.
5. So `ψ g = (ψ g)⁻¹`, and `ψ g ^ 2 = 1`.

`FiniteCupArtinComparisonRefutation.exists_character_sq_ne_one` shows that a group `G` of
order `n = 3` has a character `ψ : G →* Multiplicative (ZMod n)` and an element `g` with
`ψ g ^ 2 ≠ 1`.

- The group is cyclic of prime order (`isCyclic_of_prime_card`).
- `zmodCyclicMulEquiv` identifies it with `Multiplicative (ZMod (Nat.card G))`, and
  `ZMod.ringEquivCongr` moves to `ZMod 3`.
- The element corresponding to `1` has image `ofAdd 1`. Its square is `ofAdd 2`, which is
  not one; `decide` checks this in `ZMod 3`.

`finiteCupArtinCharacterComparisonFails` assumes `H` and derives a contradiction.

- It takes the p-adic field package `PadicField.ofField (ULift.{u} (Padic 2))` in the given
  universe.
- The published `unramifiedExtensionDegreeExistence.{u}` gives a finite Galois intermediate
  field `E` of its algebraic closure with `[E : F] = 3`.
- `IsGalois.card_aut_eq_finrank` gives `Nat.card Gal(E/F) = [E : F]`.
- The second lemma with `n = [E : F]` gives a character into `ZMod [E : F]` with a value
  whose square is not one. This contradicts the first lemma.

## Provenance and scope

The content is internal. It combines:

- the published geometric comparison;
- the canonical fundamental classes of `FiniteArtinTransferReduction`;
- the unramified-extension existence theorem;
- Mathlib's cyclic-group equivalences.

It makes no new literature claim. The refutation does not affect the published geometric
comparison or `Langlands.LocalClassField.commonClosureReciprocityExistence`, which is
proved through the geometric comparison.

This candidate also adds a falsity note to the Markdown of `FiniteArtinTransferReduction`
and `CommonClosureExistenceReduction`. Their theorems that take
`FiniteCupArtinCharacterComparison` as a hypothesis say nothing and are not to be cited.
Their Lean text is unchanged.

## Checks

The module compiles with no warnings. `finiteCupArtinCharacterComparisonFails` depends
only on `propext`, `Classical.choice` and `Quot.sound`, and has the universe parameter `u`.
