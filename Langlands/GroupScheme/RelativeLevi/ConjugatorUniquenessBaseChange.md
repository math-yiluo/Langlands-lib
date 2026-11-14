# Uniqueness of unipotent conjugators on arbitrary test schemes

Worker 639, with Worker 593 developing existence and descent separately.

This internal derived unit extends the algebraic uniqueness reduction of
`ConjugatorUniqueness` to arbitrary test schemes and arbitrary base change.
It does not prove existence of conjugators or either geometric statement
assumed by the relative wrapper.

`radicalConjugateAt l r T u`, for an actual point `u : T ⟶ U.X`, is the
all-test image of the base-changed `l`, conjugated by the image of the
section of the base-changed `U` corresponding to `u`. The identification is
the actual pullback-point equivalence `baseChangeBasePointsEquiv`.

The multiplication-isomorphism lemma rewrites the multiplication after
base change as the inverse canonical product comparison followed by the
pullback of the original multiplication. Both morphisms are isomorphisms.
For the base-change injectivity theorem, pullback preserves the two
monomorphisms, the range containment is preserved by `baseChange_mono`
and `range_baseChangeHom`, and all-test normalizer containment is preserved
by `normalizer_baseChange`. Applying the original algebraic uniqueness
criterion yields injectivity over the new base.

Composing that injective map with the inverse pullback-point equivalence
gives injectivity of `radicalConjugateAt` for every test scheme `T`.
No property of its structural map `T.hom` is needed. In particular the
argument is available on overlaps of any cover.

The relative wrapper assumes the entire propositions
`RelativeUnipotentRadicalStatement` and
`RelativeLeviSelfNormalizerStatement` at universe `u`. It uses them only
over the original base, identifies the specified radical image with the
radical image in a Levi multiplication witness, and uses closedness for
monicity. It then applies the purely algebraic base-change theorem. It
does not assert or require a proof that relative Levi, radical, reductive,
or parabolic predicates have been transported to `T`.

All constructions and proofs are derived from published pullback, subgroup
range, normalizer, and multiplication-comparison results. They introduce
no new axiom or literature assertion.
