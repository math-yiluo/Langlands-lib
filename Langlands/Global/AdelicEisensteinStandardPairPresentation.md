# Putting an aligned parabolic pair in the same standard family

`EisensteinStandardPairPresentationStatement` starts with an identification of
the two presentation tori by inverse conjugation by `w`. It supplies a point
`n` of the source torus normalizer. Conjugation by `s = n * w⁻¹` carries the
target parabolic and Levi to a standard pair for the source torus and generic
cocharacter. The new representative `s * w` is `n`. The target parabolic and
Levi keep their given domains, and the target split-component factor is
transported by the resulting torus isomorphism.

`eisensteinStandardPairPresentation` transports the simultaneous realizing
cocharacter of the target into the source torus. A rational normalizer point
moves that cocharacter into the source dominant chamber. The dynamic parabolic
and centralizer transport under the single rational conjugation and coincide
with the standard parabolic and Levi for the resulting simple-root face. The
nonnegative root signs give containment of the source minimal parabolic.

This internal reduction lets the common-family geometric lemma use the
conjugated target's actual maps and the original source presentation.
