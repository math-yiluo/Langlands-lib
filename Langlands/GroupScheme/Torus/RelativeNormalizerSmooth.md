# Smooth normalizers of relative tori over arbitrary bases

Worker 594. This internal construction supplies the smooth normalizer needed
by the smooth-affine torus Weyl quotient task.

For an arbitrary scheme `S`, a smooth relatively affine group scheme `G`, and a
closed homomorphism `t : T.toGrp ⟶ G` from a relative torus,
`relativeTorusSmoothNormalizerModel` chooses a group scheme `N` and homomorphism
`n : N ⟶ G` such that:

- `n` is a closed subgroup inclusion, locally of finite presentation;
- the structure morphism of `N` is smooth;
- `n` represents the actual published `torusNormalizer t` on every scheme test.

The relative torus is the published `RelativeTorus.IsTorus`, so it splits on an
étale cover and its finite rank may vary across that cover. There is no
restriction on the base scheme and no reductivity or maximality assumption.
This module constructs the normalizer; it does not construct the Weyl quotient.

`splitTorusNormalizer_smooth_overRing` first works over `Spec R`, with `R` any
commutative ring. It accepts a closed representative of the split-torus
normalizer whose inclusion is locally of finite presentation. The relatively
affine group is affine over this affine base and has a smooth coordinate
algebra. The ideals obtained from
`Corepresented.exists_ideal_range` cut out the torus range and normalizer range
in its affine coordinates. The split torus is identified with the
diagonalizable group of a finite free character group, giving the actual
`CharacterAction.diagonalizableEmbedding`.

The published `hasSquareZeroLifting_normalizerFamily` then supplies square-zero
lifts of normalizer points. The range and affine-coordinate comparisons identify
that family with the actual normalizer's affine points.
`formallySmooth_of_hasSquareZeroLifting` makes the coordinate quotient formally
smooth. The cut-out group and the supplied normalizer represent the same
subgroup, hence are isomorphic. Local finite presentation of the normalizer's
inclusion and smoothness of the ambient group give local finite presentation of
its structure morphism. Transporting that property to the coordinate quotient
gives a finitely presented algebra. Formal smoothness plus finite presentation
give smoothness, which is transported back to the supplied normalizer.

The existing `torusNormalizer_baseChange` from `Torus.WeylPointTransport`
combines the published base change identities for ranges and normalizers.
`splitTorusNormalizer_smooth` checks smoothness on the
affine open cover of an arbitrary base. On each chart it uses
`RelativeTorus.closedNormalizer` to obtain a closed representative with locally
finitely presented inclusion, applies the affine-base lemma, and transfers
smoothness to the base change of the given representative using uniqueness.
`relativeTorusNormalizer_smooth` repeats this argument on an étale splitting
cover. In both steps, `RelativeLevi.smooth_of_etale_cover_pullbacks` descends
smoothness. These two results apply to every representative of the normalizer,
without additional hypotheses on that representative.

Finally, `relativeTorusSmoothNormalizerModel` chooses the already published
closed normalizer from `RelativeTorus.normalizerGroupScheme` and
`RelativeTorus.normalizerHom`, and equips it with this smoothness proof.
The construction is derived from the imported Library results, rather than a
new translation of a literature statement. Its key inputs are the
arbitrary-ring diagonalizable normalizer lifting theorem in
`Torus.NormalizerLifting`, the closed relative-torus normalizer in
`Torus.RelativeGeometry`, and the published descent and representing-subgroup
uniqueness results named above.
