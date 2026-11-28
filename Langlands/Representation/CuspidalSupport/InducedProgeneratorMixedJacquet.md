# The inertial projection of a mixed Jacquet module for a maximal Levi

Let `P` and `Q` be distinct opposite rational parabolics sharing a Levi `M`, with `P` maximal proper. For an irreducible supercuspidal `π` of `M(F)`, let `Π` be the compact induction to `M(F)` of an irreducible subrepresentation of `π|_{⁰M(F)}`. Assume that no normalizer outside `M(F)` preserves the inertia class of `π`.

`mixedJacquetInertialProjection` chooses a projection `r_Q i_P Π ⟶ Π` and a section. Its accompanying proofs give the splitting identity and show that every map from `r_Q i_P Π` to an object of the inertia block of `π` factors uniquely through the projection. This is the mixed Jacquet step in the proof of Renard (2026), VI.10.1 Lemma, printed p. 207 and PDF p. 213.

The geometric filtration of VI.5.3(iii) applies because `Π` is supercuspidal. Each grade is a pullback of `Π` by a Levi normalizer and is projective by the joint special compact basis and invariance of projectivity under equivalence. The representative of the identity double coset belongs to `M(F)`, so its pullback is inner and the action of a Levi element identifies the grade with `Π`.

A normalizer preserves the common norm kernel, and pullback commutes with compact induction from it. Pulling back the norm-kernel embedding therefore puts each grade in the inertia class of the corresponding conjugate of `π`. Every other representative is outside `M(F)`. Any common irreducible subquotient of its grade and an object of the block of `π` would identify the two inertia classes. Thus every map from such a grade to an object of the block vanishes. The finite-filtration splitting lemma then gives the projection and its Hom bijection.
