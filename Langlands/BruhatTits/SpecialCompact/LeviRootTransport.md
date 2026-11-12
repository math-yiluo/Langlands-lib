# Root-group transport into the prescribed Levi

This file supplies the algebraic comparisons used by `LeviValuationRestriction` and `LeviApartmentRestriction`. The ambient group is smooth, connected and affine over an arbitrary universe-`u` field. The same split torus factors through a closed representative of a dynamic cocharacter centralizer. The representative is affine of finite type where needed for its actual root formula.

`rootSubgroup_le_centralizer_of_pairing_zero` puts an ambient root subgroup in the dynamic centralizer whenever its character pairs to zero with the defining cocharacter. Every positive integral multiple then also pairs to zero. The published `RelativeRoot.weightFiltration_one_eq_subgroup`, `RelativeRoot.dynamicSemigroupComparison` and `RelativeRoot.semigroupSubgroup_mono` turn this elementary lattice observation into containment on every test scheme.

`leviRootGroupPoints_eq_comap` applies `RelativeRoot.subgroup_comap_closedEmbedding` to the original closed inclusion, using `RelativeRoot.characterFpqc` for each nonzero character. The conclusion is the literal preimage equality in the existing rational-point groups. `map_leviRootGroupPoints` combines it with `relativeRoots_centralizer_factor dynamicLie` and the zero-pairing containment: the image is exactly the entire ambient root group. It proves equality of actual groups and not only their Lie spaces or dimensions.

`normalizingAut_leviMap` uses the published `normalizerPointsMap` and uniqueness of a normalizing torus automorphism. It identifies the actual automorphism of the same torus. `realizesReflection_leviMap` therefore preserves the full real cocharacter action, including its central directions, and the reflection predicate used by V2.

These are derived algebraic steps for KP Lemma 6.7.1 (2023), printed page 233/PDF264, rather than a separate source theorem. The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The actual valuation and apartment constructions are in the companion modules; this file proves no special-vertex or compact-preimage comparison.
