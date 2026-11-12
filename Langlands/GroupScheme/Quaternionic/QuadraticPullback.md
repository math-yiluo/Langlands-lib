# Pullback of quaternionic quadratic forms

Authors: Worker 124.

This is an internal construction derived directly from the published definitions in
`Quaternionic.Involution` and `Quaternionic.Forms`. It provides the actual change of
variables and subform operation needed for the quaternionic spin induction. It does
not assert a spin model, a Witt extension theorem, or elementary generation.

For a field `K`, a division `K`-algebra `D` with an involution of the first kind `σ`,
and finite index types, `rectangularAdjoint g` is the conjugate transpose of any
rectangular matrix `g`. On square matrices it equals the published `σ.matrix`.
The composition and involutivity lemmas are proved entry by entry using the
anti-multiplicativity and involutivity of `σ`.

`gramPullback g` is the `K`-linear map `Q ↦ g Q g*`. An element of the published
quadratic kernel has the form `a − a*`; its pullback is
`g a g* − (g a g*)*`. Consequently `quadraticPullback g` is a well-defined linear
map from `σ.QuadraticForms n` to `σ.QuadraticForms m`, without choosing any
representative. Its formula on representatives is `g Q g*`, in the Library's
row-vector convention `x ↦ x g`.

The identity and composition laws are proved by quotient induction and matrix
associativity. The shared `sesqForm_eq_dotProduct` identity is imported from
`Quaternionic.IsometryWeights`. The sesquilinear value law is proved through row-matrix and
matrix-column associativity, and passes to the quotient to give
`quadraticValue x (quadraticPullback g q) = quadraticValue (x g) q`.
The polar matrix also pulls back as `g (polar q) g*`. Finally, total singularity
of a subspace for the pullback is equivalent to total singularity of its actual
image under the `D`-linear row map for the original form. No injectivity of `g`
is required for this equivalence. No characteristic assumption is used.
