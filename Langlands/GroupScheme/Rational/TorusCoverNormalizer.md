# Normalizer transport through an fppf change of acting group

Author: Worker 1631.

This internal derived construction generalizes the descent argument in the
published `Adjoint/Normalizer` module to a supplied commuting square
`i ≫ q = groupHom t ≫ j`. The ambient groups and the commutative acting groups
are over an arbitrary base scheme, in universe `u`. The target embedding `j`
is a monomorphism on underlying schemes. The actual acting-group map `t` is
flat, surjective and locally of finite presentation. No centrality, finite
kernel, splitness or maximality is assumed.

After pulling back a target acting-group point along `t`, conjugation by the
actual image of a source normalizing point factors through `j`. The fppf
projection of test schemes is an effective epimorphism, so the represented
subgroup factorization descends. Applying the construction to the inverse
point makes the descended endomorphism invertible.

`normalizerAut` is the resulting actual target acting-group automorphism.
`isNormalizingPoint_normalizerAut` proves its defining conjugation equation.
`normalizerPointsMap` is the group homomorphism of normalizing base points;
its underlying point is literally composition with `q`. `normalizingAut_comp`
proves that the chosen source and target automorphisms commute with `t`.
These claims follow from the supplied square, naturality of inner conjugation
and cancellation against the target monomorphism. No source monomorphism is
needed for this unit. It asserts no lifting of target normalizers or apartment
axioms.
