# Block diagonal inclusions for adelic compact slices

This internal adapter complements the projection in `AdelicBlockCompactProjection` for the joint-admissibility argument of adelic block induction. It uses the specified standard compact subgroups, not arbitrarily chosen maximal compact subgroups.

`infiniteLeviCompactInclusion` is the block diagonal homomorphism from the product of the standard infinite compact subgroups of the Levi blocks to the ambient standard infinite compact. At each real or complex place, the inverse of the image equals its adjoint: on diagonal blocks this holds by the compact condition on the blocks, and off-diagonal blocks both sides are zero. Thus the image lies in the specified orthogonal or unitary subgroup. The multiplicative laws come from the block diagonal homomorphism.

`leviInParabolic_pair` checks that the block diagonal parabolic section commutes with pairing the archimedean and finite factors. The two coordinate comparisons are the published projection lemmas and jointly suffice by the adelic group splitting. The one-factor formulas `leviEmbedding_infiniteOnly` and `leviEmbedding_finiteOnly` are the ambient-group versions with the other factor equal to the identity.
