# Centralizer normalization of intrinsic conjugation cutoffs

Over any commutative ring, consider any corepresented group and an actual cocharacter. Every intrinsic subgroup for its rank-one conjugation action is normalized by the actual dynamic centralizer, on every scheme test. No field, smoothness, finite-type, or reducedness premise is used.

The coefficient-point lemmas explicitly allow a centralizer point over an arbitrary coefficient algebra; no natural global family of such points is assumed. Actual affine points commute with coefficient change. A coefficient centralizer point is fixed by the rank-one action, because it commutes with every value of the cocharacter. After extension to the universal Laurent coefficient algebra, this gives a constant twisted point.

`rankOneCutoff_isNormalizedBy_centralizer` extends this result to arbitrary scheme tests. The centralizer's actual affine ideal and the established all-test affine-cutout reflection identify its coefficient point over the test scheme's relative global sections. The constant-twisted-point conjugation lemma then preserves every intrinsic weight condition. The multiplication and inverse compatibility of the points comparison gives precisely all-test normalization.

`rankOneCutoffCentralizerAction` constructs the actual action of the affine centralizer representative on the affine representative of any such intrinsic weight subgroup, by restricting actual conjugation to the proved stable represented subgroup.

For an actual affine group in any supplied affine presentation, `cyclicConjugationCutoff_isNormalizedBy_centralizer` transports the normalization back to the original group, again on every scheme test and allowing arbitrary test-dependent centralizer points. This is centralizer normalization, not yet normalization by the full dynamic parabolic.

Provenance: internal consequence of actual dynamic centralizer commutation, arbitrary-ring affine-cutout reflection, the established intrinsic constant-twisted-point conjugation lemma, and represented stable actions.
