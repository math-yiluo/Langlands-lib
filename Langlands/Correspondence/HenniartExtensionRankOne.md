# Rank one and the extended stable map

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtensionRankOne`,
namespace `Langlands.Henniart.Extension`.

Henniart (2000), §4.1, last sentence ("pour `χ ∈ G⁰_F(1)` d'ordre fini, `π(χ)`
est bien le caractère de `F^×` tel que `χ ∘ ...`"), and the character clause of
3.8 (c), extended to all characters by twisting.

`trivialWeilBasis K e` is the rank-one Weil class of the trivial field
character pulled back along `e` (published `rankOneWeilCharacterClass`).

- `trivialWeilBasis_isUnitary`: it is unitary. Its character line has image
  `{1}`, which is finite, so the published `isUnitary_of_hasFiniteImage`
  applies.
- `trivialWeilUnitary_isFiniteFactoring`: it factors through the trivial
  quotient `PUnit` of the absolute Galois group, via the trivial character line.

`extensionMap_trivial`: assume stable images in every rank and unramified-twist
independence, and let `e` be geometric. The extension sends the trivial class to
the published `rankOneSupercuspidalClass K 1`. By `extensionMap_agrees`, the
extension is the stable image `y`. A candidate `Φ` at the quotient of the stable
image satisfies the character clause of 3.8 for the trivial character
(`LatticeMap.CharacterCompatibility`). It provides a domain element whose
inclusion is the generator of the trivial Weil class, which by injectivity of the
published `Weil.includeUnitary` is the generator itself, and whose image includes
to the generator of `rankOneSupercuspidalClass K 1`. Since `Φ` sends the
generator to `y`, the two basis classes agree.

`extensionMap_rankOne`: the published `SupercuspidalRankOneCompatibility`. By
the published `supercuspidalRankOneCompatibility_iff_eq`, it suffices to show
that the extension in rank one is the published `rankOneReciprocityEquiv K e`.
Every rank-one class is `rankOneWeilCharacterClass K e χ`
(`rankOneWeilCharacterClass_surjective`). That class is the twist of the
trivial class by `χ ∘ rec`: the published `IsRankOneWeilCharacter.twist` and
`IsRankOneWeilCharacter.class_unique` identify them. Twist compatibility of the
extension (`extensionMap_twist`) and of the reference bijection (published
`rankOneReciprocityEquiv_twist`), together with `extensionMap_trivial` and
`rankOneReciprocityEquiv_character`, give equality.
