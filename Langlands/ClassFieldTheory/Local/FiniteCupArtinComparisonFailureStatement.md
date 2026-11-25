# Failure of the arithmetic inverse-cup character comparison

`Langlands.ClassFieldTheory.Local.FiniteCupArtinCharacterComparisonFails.{u}` is the
proposition `¬ FiniteCupArtinCharacterComparison.{u}`. It is a proposition definition, not
a theorem. It has the single universe parameter `u` of the negated proposition.

The negated proposition `FiniteCupArtinCharacterComparison` (module
`Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonStatement`) says the following.
Take any prime, any p-adic field package `F` with carrier in universe `u`, any finite
Galois extension `D/F` in that universe, any class `c` with the positive invariant
`1 / [D : F]` for `FiniteArtinSymbol.relInv F D`, and any certificate that its degree
minus two cup map is bijective. Then for every character
`ψ : Gal(D/F) →* Multiplicative (ZMod [D : F])` and every unit `a` of `F`,
`arithmeticReciprocityOfCup`, applied to the norm class of `a` and evaluated by `ψ`
through the abelianization, equals `Multiplicative.ofAdd (FiniteArtinSymbol.symbolValue ψ a)`.
`FiniteCupArtinCharacterComparisonFails.{u}` says that this does not hold for every such
datum in universe `u`.

## Provenance

The content is internal. `FiniteCupArtinCharacterComparison` is false: the Library's
comparison with the true sign is `FiniteGeometricCupArtinCharacterComparison`, which uses
`geometricReciprocityOfCup`, the inverse of `arithmeticReciprocityOfCup`. This module only
states the refutation and proves nothing. Its proof is the theorem
`finiteCupArtinCharacterComparisonFails` (module
`Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonFailureProof`).
