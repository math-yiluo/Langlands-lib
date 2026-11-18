# Étale points tested on affine étale target charts

This internal algebraic reduction is derived from the Library's relative
morphism-property definitions and scheme descent. It uses no analytic
comparison theorem.

`isEtale_of_affine_target_tests` says that a point of an algebraic space
represented by any scheme is étale if the actual pullback projection to
each affine étale target chart is étale. A fixed surjective étale atlas
reduces the conclusion to a property of one scheme projection, using
`relativeProperty_of_etale_atlas` and scheme étale descent. The affine open
cover of that atlas pulls back to an open cover of the projection's source.
Each member is identified with the represented pullback to the
corresponding affine chart by the two pullback universal properties.
The assumed étaleness of that projection, composition with the open
immersion, and source Zariski locality prove the result.

Scheme étale descent comes from Mathlib's faithfully flat descent and the
published `SchemeFlatPropertyDescent.descendsAlong_etale_surjective`.
The statement needs no separatedness or finite-type condition; such
conditions are only needed later to express its pullbacks as finite-type
affine test algebras for analytification.
