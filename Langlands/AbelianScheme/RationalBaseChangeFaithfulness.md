# Faithfulness of actual rational Hom pullback

`RationalBaseChangeIsFaithful b` is the Prop-valued predicate that the existing actual rational Hom pullback `rationalBaseChangeHom b` is injective for every pair of abelian schemes on the base of `b`.

This internal helper first assumes that the actual scheme pullback functor `Over.pullback b` is faithful. The theorem `baseChange_map_injective_of_faithful_over` forgets actual abelian-scheme homomorphisms to their group-object maps in the over-category and uses that faithful pullback. The group-object forgetful map and additive notation reflect the resulting equality.

`rationalBaseChangeHom_injective_of_faithful_over` writes the integral Hom pullback as an integer-linear map. Flatness of `Q` over `Z` preserves its injectivity after tensoring on the left with `Q`. Tensor induction identifies this map with the existing actual rational Hom pullback. The theorem `rationalBaseChangeIsFaithful_of_faithful_over` packages the result for all pairs.

`rationalBaseChangeIsFaithful_of_fpqc` applies Mathlib's faithful scheme pullback instance for a surjective, flat, quasi-compact morphism. `rationalBaseChangeIsFaithful_field` specializes it to every morphism between spectra of fields: the target has one point and the source is nonempty, so the map is surjective; a scheme over a field is flat and a morphism between these affine schemes is quasi-compact. Neither algebraic closedness nor characteristic zero is required.

`rationalBaseChangeHom_ne_zero_field` records the nonzero reflection needed for the Rosati positivity argument. It applies to every actual rational homomorphism, including endomorphisms, and to every field extension, including pullback along an identity morphism.

All schemes, fields and actual abelian schemes retain universe `u`. This unit is an internal derivation from Mathlib's fpqc faithful pullback theorem, flatness of rational scalar extension, and the Library's actual group and rational Hom constructions. It makes no claim about trace rationality or positivity.
