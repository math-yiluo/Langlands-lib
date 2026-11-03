# Twisting characters by grouplike families, and conjugation of character points

## Twists

Let `B` be an `R`-algebra and `s : Multiplicative M →* B[M]ˣ`. For a `B`-algebra `x : B ⟶ D` and a character `t : Multiplicative M →* Dˣ`, `twist s x t` is the character `m ↦ evaluate x t (s m)`. When `s` has grouplike values (`IsGrouplikeHom s`), this is the action on `D`-points of the endomorphism of `D(M)` over `B` described by `s`.

- `twist_mul`, `twist_one`: for grouplike `s`, twisting is a group homomorphism in the character.
- `mapCharacter_twist`: twisting is natural in the `B`-algebra.
- `twist_coefficientMap`: twisting by the image of `s` under `π : B ⟶ B'` is twisting by `s` through `π`.
- `twist_constant_universal`: the twist of the universal character over `B[M]` is `s` itself. `twist_universal`: twisting by the universal monomials is the identity.
- `isGrouplikeHom_of_twist`: conversely, a family whose twists are multiplicative and unital in the character has grouplike values. The proof applies the hypothesis to the universal pair of characters over `B[M][M]`.
- `twist_twist` and `IsGrouplikeHom.twist`: twisting twice is the twist by `twist s (constant B) s'`, which is again grouplike. `isGrouplikeHom_universal`: the universal family is grouplike.

## Lifting

For `π : C ⟶ D` whose kernel consists of nilpotent elements:

- `isGrouplikeHom_lift_unique`: grouplike families over `C` with the same image over `D` are equal.
- `exists_isGrouplikeHom_lift`: if `π` is moreover surjective, every grouplike family over `D` is the image of a grouplike family over `C`. Elementwise lifts exist by `exists_isGrouplike_lift`. They form a group homomorphism by uniqueness, since products of grouplike lifts are grouplike lifts of products.

## Conjugation of embedded characters

A `CharacterEmbedding F M`, for a group functor `F` on commutative `R`-algebras, is a family of group homomorphisms `hom D : (Multiplicative M →* Dˣ) →* F D`. It is natural in `D` (`naturality`) and injective on points over each algebra (`injective`). `range D` is its image. This is the algebra-level form of a diagonalizable subgroup.

Let `g ∈ F A` be such that conjugation by `F.map f g` maps embedded characters to embedded characters, for every `f : A ⟶ D`. Then:

- `conjChar ι hg f t` is the unique character with `ι(conjChar f t) = F.map f g * ι t * (F.map f g)⁻¹` (`hom_conjChar`). It is multiplicative (`conjChar_mul`), unital (`conjChar_one`) and natural (`mapCharacter_conjChar`), all by injectivity of `ι`.
- `conjUniversal ι hg` is its value at the universal character over `A[M]`. `conjChar_eq_twist` shows that conjugation is the twist by this family, and `isGrouplikeHom_conjUniversal` that the family is grouplike.

## Provenance

This is an internal construction toward task `0f453442`. Mathematically, conjugation by a normalizing point gives an endomorphism of the diagonalizable group over `A`. Such endomorphisms are given by grouplike families, and they lift uniquely along nilpotent thickenings: the automorphism functor of a diagonalizable group is formally étale. The module formalizes this rigidity at the level of algebra points.
