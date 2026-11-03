# Correcting a Borel-normalizing point to normalize a maximal torus

This internal reduction retains the exact relation between a given normalizing
point and its torus correction. It does not prove the Borel normalizer theorem
or the conjugacy of maximal tori.

Over an arbitrary field, `exists_mul_mem_normalizerPoints_of_overgroupIso`
takes a homomorphism `i : B ⟶ G`, a maximal torus `f : T.toGrp ⟶ B`,
the property `MaximalToriAreConjugate B`, a rational point `x` of `G`,
and an actual automorphism `φ` of `B` satisfying
`i ≫ Int(x) = φ.hom ≫ i`. It produces a rational point `p` of `B` for which
`(p ≫ i.hom.hom) * x` belongs to `normalizerPoints (f ≫ i)`.
No closedness or Borel hypothesis on `i`, ambient maximality of `f ≫ i`,
or smoothness, affineness or connectedness of `G` is needed for this lemma.

The proof conjugates the maximal tori `f ≫ φ.hom` and `f` inside `B`.
If `p` and `e` give that conjugacy, the inner-automorphism composition and
homomorphism identities show that the corrected point acts on the original
embedded torus through `e`. The group-scheme source isomorphism is viewed as
an isomorphism of commutative group schemes, as required by `normalizerPoints`.

For a Borel inclusion over an algebraically closed field,
`IsBorelSubgroup.torusNormalizerCorrection` chooses such a point `p`.
Its input `x` lies in the ordinary abstract normalizer of the image of `B(k)`.
The published `conjugatingIsoOfMemNormalizer` construction supplies the actual
Borel automorphism and its compatibility with ambient conjugation. The result
is a subtype of actual `B(k)` points; its property records that left
multiplication of the original `x` by the image of the chosen point normalizes
the fixed torus.

`IsBorelSubgroup.pointNormalizer_eq_of_torusNormalizer` reduces the abstract
point-normalizer equality for this Borel to membership of points simultaneously
normalizing the Borel's point image and its fixed maximal torus.
The corrected point still normalizes the Borel because its correcting factor
belongs to `B(k)`. The explicitly assumed simultaneous-normalizer result puts
the corrected point in `B(k)`. Multiplying by the inverse correcting factor
returns membership of the original point. The reverse inclusion is the
ordinary fact that a subgroup normalizes itself.

The existing `SubgroupConjugate.normalizerCorrection` concerns maximal split
tori and returns a normalizing point realizing a supplied existential subgroup
conjugacy. The present reduction instead uses a fixed original point and
retains its multiplication relation with the correction; this is needed for
the final membership cancellation. It uses ordinary maximal tori and an
individual-group conjugacy premise.

All content is derived from the imported actual subgroup-conjugacy,
maximal-torus transport, inner-automorphism and rational Borel-normalizer
constructions. The conjugacy property and the simultaneous-normalizer
membership assertion remain explicit premises. No new external structural
input or unconditional self-normalizer theorem is asserted.
