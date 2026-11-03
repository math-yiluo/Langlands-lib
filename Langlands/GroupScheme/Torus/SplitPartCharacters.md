# Rational characters on the split part of a torus

This derived result combines the published rational-character detection theorem
`CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus` with the
universal property `IsLargestSplitSubtorus`. It uses no new assertion from the
literature.

Let `T` be a torus over any field, with affine structure morphism locally of
finite type. If `i : A → T` is its largest split subtorus, then restriction
`characterRestrict i` on rational characters is injective. In particular a
rational character of `T` that vanishes on `A` is zero. The theorem concerns
characters defined over the original field. It asserts no such injectivity for
all characters over a splitting field.

The implemented proof reduces injectivity to a trivial kernel. A nonzero
rational character is detected by a rational homomorphism `φ : Gm → T` using
the published detection theorem. The largest split subtorus factors this
actual homomorphism through `i`, even when `φ` is not an embedding.
Functoriality of restriction then contradicts vanishing on `A`.

The construction `IsLargestSplitSubtorus.characterRestrictEquivRange` identifies
the rational characters of `T`, as an additive group, with the image of this
restriction map inside the characters of `A`. Its forward map is exactly
restriction, as the accompanying evaluation lemma states. It uses the standard
additive-group equivalence with the range of an injective homomorphism and
does not assert that every character of `A` extends to `T`.

The second theorem gives the same conclusion for every maximal split subtorus
of `T`, using the published fact that such a subtorus has the largest split
subtorus universal property. Affineness of the total space follows from the
assumed affine structure morphism.

All morphisms are morphisms of group schemes and the field and its universe are
arbitrary. This proves the rational-character detection step for a torus's
split part; the unipotent weight, central-torus, centralizer, and ambient
maximality arguments in the host task remain separate obligations.
