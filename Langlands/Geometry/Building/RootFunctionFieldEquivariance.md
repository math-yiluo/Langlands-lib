# Equivariant restriction of actual root-function families

For arbitrary fields k and K in universe u, actual field restriction evaluates
an upstairs family on the pulled-back character and the extended original
rational point. This internal unit packages that same function as equivariant
maps for the two existing actions.

For a supplied split torus, fieldRestrictTranslationHom uses the inverse of
the actual real cocharacter base-change equivalence on translation vectors.
The existing fieldRestrict_vadd identity and surjectivity of that equivalence
prove equivariance for every upstairs vector.

For any subgroup homomorphism i whose underlying scheme map is a monomorphism,
fieldRestrict_normalizer proves equivariance through the actual
normalizerPointsFieldExtend. Character pullback commutes with the Weyl action,
and rationalExtend preserves multiplication and inversion, so it preserves
the conjugated argument in the family formula. fieldRestrictNormalizerHom
restricts the existing upstairs action along this actual normalizer map and
packages the unchanged fieldRestrict as an equivariant function. This part
requires no splitness, smoothness, affineness or root-valuation hypothesis.

The provenance is internal composition of the published action definitions,
the actual normalizer and cocharacter base-change comparisons, and the literal
family restriction. No new assertion from original literature is added.
Neither equivariant-map construction proves that restriction is a root-datum
valuation or constructs an apartment, fixer comparison or supplied-model
building comparison. These remain separate obligations.
