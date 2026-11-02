# The degree-one twist under relative projective linear actions

For any commutative ring `K`, any scheme `S` with a specified morphism
`a : S → Spec K`, any natural number `n`, and any `K`-linear automorphism `e`
of `Fin (n + 1) → K`, the definition `relativeLinearActionTwistIso a e`
constructs an actual module-sheaf isomorphism

```text
(linearAction a e)^* O(1) ≅ O(1)
```

on the existing relative projective space over `S`. Here `O(1)` is the actual
`RelativeProjectiveSpace.twistOne S n`, pulled back from the integral model.
The coefficient ring and scheme have the same arbitrary universe. There is
no field or nontrivial-ring hypothesis.

The changed coordinate section with index `i` is the sum over `j` of the
original coordinate section with index `j`, multiplied by
`scalarsFromBase (toBase S n ≫ a) (e (Pi.single j 1) i)`.
The theorem `relativeLinearActionTwistIso_coordinate` proves that the
comparison sends the pulled-back coordinate with index `i` to this section.
This is the row convention of the existing polynomial and relative actions.

The relative coordinate identity and coefficient projection formula identify
the polynomial linear-system map of the actual relative coordinates with the
existing polynomial projection. The coordinate-change law then identifies
the relative linear-system map of the changed coordinates with the existing
relative action. Equality transport of the actual relative linear-system
twist isomorphism constructs the comparison. `pullbackCongrCoordinateIso`
packages equality transport of an isomorphism together with its section law.
Specializing this construction gives `relativeLinearActionTwistData`, from
which the isomorphism and coordinate formula are projected.

The comparison at the identity linear map equals equality transport along
`linearAction_refl` followed by the canonical identity-pullback comparison.
It commutes with every further `K`-linear combination of the coordinates,
including combinations whose linear map is not invertible. The proof uses
the fact that `linearAction a e` preserves `toBase S n ≫ a`, hence fixes every
coefficient pulled back from `K`.

The composition theorem is an equality of actual module-sheaf morphisms.
Pulling back the comparison for `f` along the action of `e`, then composing
with the comparison for `e`, equals the comparison for `e.trans f` after the
canonical `pullbackComp` and equality comparison for `linearAction_comp`.
Thus `e.trans f` denotes `f` after `e`, matching the existing scheme-action
composition law.

The generic helpers `pullback_comparison_refl`,
`pullback_comparison_linearChange`, and
`linearChange_pullback_comparison_comp` implement these proofs on an abstract
line bundle. Equality of sheaf maps follows from equality on a covering
family of actual frames and its pullbacks, by the previously proved section
extensionality and pullback-composition results. Additivity, scalar
compatibility, and `linearChangeSections_comp` give the coordinate
calculation. Specializing these helpers avoids repeatedly unfolding the
concrete integral-model pullbacks in the coherence proofs.

The abbreviation `globalLinearActionTwistIso S n e` specializes the comparison
to `a := S.toSpecΓ`. It applies to the existing `globalLinearAction` with
matrix entries in the ring of all global functions on `S`. Its coordinate,
identity and composition laws are the relative laws at this value of `a`.

The source assertions are derived from the imported constructions; there is
no new external assertion. Naturality under changes of base and of coefficient
ring, the tautological line bundle on a glued projective bundle, and the
ordinary large-level moduli representability theorem remain further
obligations.
