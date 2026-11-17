# Detection on every analytic étale object

This is an internal sheaf-theoretic consequence of the existing analytic étale
site, field-valued points, and Mathlib's filtered-colimit fibre construction. It
is derived content rather than a verbatim literature assertion. The argument
extends the identity-object method of `AnalyticEtaleGlobalGerms` to every object;
it does not use the analytic equivariant comparison or any result assuming it.

`eq_of_etalePointGerms_eq` fixes an arbitrary étale object `U` and assumes
surjectivity of `pointProjection L U.left`. For sections `s` and `t` it forms the
sieve of arrows on which their restrictions agree. Given any ordinary point of
`U`, choose an `L`-valued representative `p`, and let `x` be its image in the
base. Equality of the two germs at the lift `p` is equality in a filtered
colimit. Mathlib's `toPresheafFiber_eq_iff'` supplies an étale neighborhood on
which the restrictions agree, still carrying a lift of `p`. Naturality of
`pointProjection` shows that this neighborhood's point maps to the prescribed
ordinary point of `U`. The sieve is therefore jointly surjective and covering.
The sheaf's separatedness proves equality of the sections, implemented by
comparing the linear maps from `R` taking `1` to `s` and `t`.

`etalePointFibers_jointlyFaithful_of_objectwise_surjective` assumes this
surjectivity for every étale object. For two morphisms inducing the same maps on
all point fibres, naturality of `toPresheafFiber` proves equality of the germs
of their values on every section over every object. The first lemma gives
equality of those values, hence equality of the morphisms. The geometric
surjectivity assumption is explicit in this helper; it must be proved from the
original base-space assumptions when assembling the final target.

The coefficient and fibre universe is `max u (v + 1) uL`; the field, analytic
space, and extension-field universes remain independent.
