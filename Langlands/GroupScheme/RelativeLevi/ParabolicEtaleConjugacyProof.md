# Etale-local conjugacy of relative parabolic subgroup schemes

Worker 648, with the compatible-presentation and equal-fibre constructions of
Worker 598 and their cited supporting constructions.

`relativeParabolicEtaleLocalConjugacyStatement` proves the unchanged
`RelativeParabolicEtaleLocalConjugacyStatement` in every universe. The base
scheme is arbitrary, the ambient group is reductive, and the two inclusions
satisfy the published relative parabolic predicate. The conclusion concerns
equality of subgroup ranges on every test scheme.

The proof lifts the prescribed residue-field conjugator to an actual section
on a pointed étale neighbourhood using `pointedEtaleConjugator`. Conjugating
the first pulled-back inclusion by that section gives two relative parabolic
inclusions whose ranges agree at the supplied field-valued point. Relative
parabolicity is preserved by base change and by the inner automorphism.

The range equality is reflected to the canonical residue field of the image
point by `SubgroupFunctor.range_eq_residue_of_fieldPoint`. Its monomorphism
hypotheses follow from relative parabolicity. The imported
`relativeParabolicConjugacyOfEqualResidue` then supplies conjugacy on a further
étale neighbourhood.

The helper `Dynamic.EtaleSubgroupConjugacyData.preconjugate` composes this second
conjugator with the pullback of the lifted original section. If the second
section is `h` and the original lifted section is `g`, the resulting section is
`h * g`: the published `innerIso_mul_hom` identifies its inner automorphism with
the composite of inner conjugation by `g` and then by `h`. The exact
`baseChange_innerIso_hom` equation identifies the pulled-back first inner
automorphism.

Finally, `EtaleSubgroupConjugacyData.comp` composes the two étale projections
and transports the section through the canonical pullback comparison. The
pointed lift equation shows that the composite neighbourhood contains the
original point. This yields precisely the existential data in the target
statement.

This proof composes the imported constructions and transport lemmas. It uses
no additional base or group hypotheses and changes neither the target
statement nor its imported definitions.
