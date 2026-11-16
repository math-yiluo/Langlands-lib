# Relative smoothness of actual equivariant maps

This is an internal consequence of the actual affine-action constructions and
the relative graded square-zero lifting results. It works in every universe over
an arbitrary commutative ring `R`.

Let `X` and `Y` be affine schemes over `Spec R`, with actual multiplicative-group
actions `s` and `t`. Suppose that the supplied morphism `f : X ⟶ Y` is
equivariant, that both structure morphisms `X → Spec R` and `Y → Spec R` are
smooth, and that `f` is smooth. Then the actual induced morphisms
`X⁺ → Y⁺` and `X⁰ → Y⁰` on the previously constructed attracting and fixed
schemes are smooth. These are the same representing schemes whose closed
inclusions characterize attraction and fixedness on every relative scheme
test; the theorem does not replace them by a rational-point construction.

The algebraic part starts with natural unit actions on two commutative
`R`-algebras `B` and `C` and a map `B → C` commuting with their actual Laurent
coactions. `attractingAlgebraMap` and `fixedAlgebraMap` are the induced maps of
the negative-coefficient and fixed-equation quotients. Their values on quotient
classes are the classes of the images under the original map. The
`coaction_map_apply` identity converts categorical coaction equivariance into
the elementwise condition of `RelativeGradedFormallySmooth`.

If the original algebra map is formally smooth, the quotient maps are formally
smooth by `formallySmooth_negQuotientMap` and
`formallySmooth_offQuotientMap`. The required homogeneous-coefficient identities
come from the action laws, and the coefficient-sum identity comes from its
counit. In particular this formal-smoothness step does not require smoothness
of `B` and `C` over `R`.

For the algebraic smoothness conclusions, both `B` and `C` are additionally
smooth over `R`. The earlier absolute smoothness results make both quotients
smooth over `R`, hence finitely presented. The helper
`AffineSchemeCoordinates.finitePresentation_hom` proves that a map from a
finite-type `R`-algebra to a finitely presented `R`-algebra is finitely presented,
using `RingHom.FinitePresentation.of_comp_finiteType`. This supplies finite
presentation for each quotient map. Formal smoothness and finite presentation
then give its smoothness.

For the actual scheme morphism, the coordinate algebra map is contravariant:
it runs from the coordinates of `Y` to those of `X`.
`algSpec_attractingAlgebraMap` and `algSpec_fixedAlgebraMap` identify the spectra
of its quotient maps with `schemeActionAttractingMap s t hf` and
`schemeActionFixedMap s t hf`. Each proof cancels the target's closed
monomorphism into `Y`. The affine point equivalence and its naturality reduce
the resulting equality to the quotient maps' values on classes.
Finally `smooth_schemeActionAttractingMap` and `smooth_schemeActionFixedMap`
transfer the proved algebraic smoothness to the actual morphisms through
`HasRingHomProperty.Spec_iff`.

The hypotheses explicitly include smoothness of both original schemes over
the base as well as smoothness of `f`. No field, characteristic, reducedness,
noetherian, or nontrivial-action hypothesis is imposed. This unit does not prove
orbit closedness, reductive quotient affineness, or
`DynamicQuotientProperStatement`; it uses none of the excluded
regular-cocharacter/Borel or rank-one inputs.
