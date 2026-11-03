# Square-zero lifting for normalizers of diagonalizable subgroups

Let `F` be a group functor on commutative `R`-algebras corepresented by a formally smooth algebra `B`, and `ι` a `CharacterEmbedding` of a diagonalizable group. This module proves that the algebra-level normalizer family `normalizerFamily ι.range` of the embedded characters (from `CorepresentedNormalizer`) has the square-zero lifting property `HasSquareZeroLifting`. The centralizer is treated in Worker 1296's `CentralizerSmooth`.

## Normalizer

- `exists_conj_of_mem_normalizerFamily` and `exists_conj_inv_of_mem_normalizerFamily`: a normalizing point and its inverse conjugate embedded characters to embedded characters after every refinement.
- `conjChar_conjChar`: conjugating by `g` and then by `g⁻¹` is the identity on characters.
- `hasSquareZeroLifting_normalizerFamily`: let `g₀` normalize the embedded characters over `C ⧸ N`, with `N ^ 2 = 0`. Write `s̄` and `s̄'` for the grouplike families of conjugation by `g₀` and by `g₀⁻¹` (`conjUniversal`).
  1. Lift `s̄` and `s̄'` to grouplike families `s` and `s'` over `C` (`exists_isGrouplikeHom_lift`).
  2. `g₀` is a twisted transporter for `s`, so `exists_twisted_lift` gives `g ∈ F C` reducing to `g₀` with `ι(twist s t) * F.map f g = F.map f g * ι(t)` for all `f : C ⟶ D` and characters `t`.
  3. The composite `twist s (constant C) s'` is grouplike. It reduces to the universal family over `C ⧸ N` by `conjChar_conjChar`, so it is the universal family over `C` by uniqueness of grouplike lifts. Hence `twist s f (twist s' f t) = t`.
  4. Therefore conjugation by `F.map f g` and by its inverse both preserve the embedded characters, so `g` lies in `normalizerFamily ι.range C`.

## Diagonalizable subgroups of corepresented groups

For a homomorphism `j : D(M) ⟶ Spec B` from the published diagonalizable group scheme `Diagonalizable.groupScheme R M`, which is a monomorphism of schemes:

- `diagonalizableEmbedding e j` is the character embedding `t ↦ (characterPoint t ≫ j)` in affine coordinates. `characterPoint` is published in `AffineCharacterAction`. Naturality follows from `characterPoint_mapCharacter` and the naturality of `affinePointsEquiv`; injectivity from `j` being a monomorphism.
- `diagonalizableEmbedding_range`: its range over `A` is the published family `affineSubgroups (range j) A`, the points of `range j` over `Spec A`.
- `SubgroupFunctor.range_iso_comp`: precomposing a homomorphism with an isomorphism does not change its range.

## Provenance

This is an internal construction toward task `0f453442`. For a torus in a smooth group over a field, it gives the infinitesimal lifting property behind the smoothness of the normalizer (Milne, *Algebraic Groups* (2017), Corollary 13.10). Milne deduces the normalizer case from the centralizer through equality of identity components. The implemented proof instead lifts the conjugation action directly, using rigidity of diagonalizable groups (grouplike lifting) and the twisted transporter lifting of `TwistedLifting`. It holds over an arbitrary base ring `R`, for every additive commutative group `M`.
