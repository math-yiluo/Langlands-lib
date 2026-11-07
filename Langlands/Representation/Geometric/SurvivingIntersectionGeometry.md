# The entire source Levi in a surviving represented intersection

This internal geometric unit identifies the coefficient group in a surviving piece of the represented geometric lemma. It starts with the existing `GeometricLemmaIntersectionDatum D` for source `p : P ⟶ G` with Levi `l : M ⟶ P`, target `q : Q ⟶ G` with Levi `lQ : L ⟶ Q`, and representative `z`. The datum supplies actual intersection group schemes and their geometric identities. Its existence remains an input.

The additional hypothesis is the all-test equality `SubgroupFunctor.range D.p' = ⊤`. It says that the source intersection parabolic is the entire original source Levi scheme. This is precisely the alternative to the proper-source case. The unit derives radical triviality and the full conjugate-Levi identification from this hypothesis; it does not assume either conclusion.

`sourceRadical_range_eq_bot_of_full` proves

`SubgroupFunctor.range (D.r' ≫ D.p') = ⊥`.

The radical of the intersection parabolic is smooth, connected, unipotent and normal. Its composite into the original source Levi is a closed subgroup. The published normal-image theorem makes it normalized by the range of `D.p'`; the fullness hypothesis makes that range the whole source Levi. The original source Levi is connected reductive by `hl`, and hence has trivial ground-field unipotent radical over any field. Its defining radical-triviality property therefore kills this actual composite on every test scheme. No characteristic, perfectness, algebraic-closure or local-field restriction is introduced in this argument.

`sourceLeviPoints_eq_source_of_full` then proves that the literal ambient rational-point image of `D.l' ≫ D.p' ≫ l ≫ p` equals the entire original source Levi image `pointImage (l ≫ p)`. Every source point lifts through `D.p'` by the all-test fullness hypothesis. The datum's original multiplication isomorphism writes that lift as a Levi point times a radical point. The radical point has trivial image by the preceding theorem. Mapping this factorization into the original ambient group gives the required original Levi representative.

Combining this equality with the datum's existing source intersection-Levi identity proves `sourceLevi_le_conjugate_targetLevi_of_full`: the full source Levi point subgroup lies in the conjugate of the original target Levi. Consequently, `targetLeviPoints_eq_conjugate_source_of_full` identifies the actual target common-Levi subgroup

`pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom`

with the full conjugate of `pointImage (l ≫ p)`.

`survivingIntersectionConjugationEquiv` turns this derived equality into an actual topological-group isomorphism from the target common Levi to the entire original source Levi image. It uses the existing literal-conjugation construction. Its value at an ambient target point `x` is `z * x * z⁻¹`; the `_apply_coe` theorem proves this on the original point carriers. Finally, `targetLeviPointsToSourceLevi_eq_survivingConjugation` identifies this isomorphism with the datum's original geometric coefficient map, and `targetLeviPointsToSourceLevi_surjective_of_full` proves that map is surjective. Its surjectivity is a conclusion.

The algebraic results omit the unused Hausdorffness, affineness and ambient local compactness and nonarchimedean hypotheses of the surrounding represented-geometric interface. The topological equivalence uses the inherited subgroup topologies and the ambient topological-group structure available from that interface; its representative formula and the resulting surjectivity do not require Hausdorffness or local compactness. The field and group schemes share universe `u`.

The provenance is internal. The proof composes the published normal-image theorem, the proved implication from connected reductivity to ground-field radical triviality, the datum's actual multiplication and intersection identities, and literal conjugation. It identifies the full original source Levi, so the universal-family application can retain the original rational-norm coefficient algebra. No coefficient representation, admissibility or scalar-extension conclusion is assumed or proved here. Adapted-representative existence, finite ordered orbit geometry, native compact orbit-Jacquet comparison and the global fixed-module finiteness theorem remain separate obligations.
