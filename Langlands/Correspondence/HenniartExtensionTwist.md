# Character twists and the extended stable map

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtensionTwist`.

Henniart (2000), §4.3 ("π(σ (χ ∘ rec)) = π(σ) χ ... découle aussi de 3.8"),
extended to all quasi-characters through unramified twists as in §4.4 and
Henniart (1993), §4.3.

## Helper lemmas

`Supercuspidal.twistBasisEquiv_congr` (namespace
`Langlands.VirtualRepresentation.Supercuspidal`): rank-wise twists by equal
families of characters agree. The open-kernel and determinant-kernel proofs are
propositions.

In namespace `Langlands.Henniart.Extension`:

- `supercuspidalTwistBasis K χ` is the rank-wise twist by `χ ∘ det`;
  `supercuspidalTwistBasis_mk` identifies it in each rank with the published
  `supercuspidalTwist`.
- `supercuspidalTwistBasis_comp`: twists compose to the twist by the product, by
  the published `supercuspidalTwist_twist`.
- `unramifiedTwistBasisEquiv_eq`: the published unramified twist by `z` is the
  twist by `fieldUnramified K z` (definitional).
- `reciprocityHom_surjective'`: the reciprocity homomorphism is surjective
  (the abelianization map is surjective and the candidate is an isomorphism).
- `weilCharacter_mul` (definitional) and `weilCharacter_mul_comm`: pulling back
  is multiplicative and Weil characters commute.

## Compatibility with all quasi-characters

`extensionBasis_twist`: assume candidate existence, stable images in every rank,
unramified-twist independence and a geometric candidate `e`. For every
quasi-character `χ` of `K^×` and every class `b`, the extension of the twist of
`b` by `χ ∘ rec` is the twist of the extension of `b` by `χ ∘ det`.

Proof. Let `b = z b₀` be a stable decomposition with image `π₀`. Decompose the
twist of `b₀` by `χ ∘ rec` with the published
`LocalWeil.unramifiedTwistFiniteFactoring` as `w u₁`, with `u₁` unitary of finite
image, and take a stable image `π₁` of `u₁`. Put `χ₁ = χ · fieldUnramified(w⁻¹)`.
Under the geometric candidate, the twist of `b₀` by `χ₁ ∘ rec` is `u₁`
(`weilCharacter_fieldUnramified`). Since `b₀` and `u₁` are both unitary, the
published `Weil.norm_eq_one_of_isUnitaryClass_twist` and the surjectivity of
reciprocity show that `χ₁` has modulus one. A common candidate for `b₀` and `u₁`
sends the `χ₁`-twist of `b₀`, which is `u₁`, to the `χ₁`-twist of `π₀`
(`candidate_twist_generator`). So `π₁` is that twist. The twist of `b` by
`χ ∘ rec` is `(z w) u₁`, which is a stable decomposition with image `π₁`. Hence
its extension is the twist of `π₀` by `(fieldUnramified(z w) · χ₁) ∘ det`, and
this character equals `χ · fieldUnramified(z)`. The last step is a computation
of `w ^ k`, `(w⁻¹) ^ k` and `(z w) ^ k` with `k = ord(a)`.

`extensionMap_twist`: the published `SupercuspidalTwistCompatibility` for `e`,
through `supercuspidalTwistCompatibility_iff` and `sigma_extensionMap`.
