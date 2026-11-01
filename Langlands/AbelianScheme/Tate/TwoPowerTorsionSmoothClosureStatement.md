# Smooth scheme structure on the actual torsion closure

`Langlands.AbelianScheme.Tate.TwoPowerTorsionSmoothClosureStatement.{u}`
asserts the following for every algebraically closed field `K : Type u`
and every actual bundled abelian scheme `A` over `Spec K`. There are a
scheme `Y : Scheme.{u}` and a closed immersion `i : Y ⟶ A.X.left`
whose underlying image is exactly `closure (twoPowerTorsionLocus A)`
and for which the composite `i ≫ A.X.hom : Y ⟶ Spec K` is smooth.
The closure and the locus are the existing actual scheme topology and
actual sections killed by some power of two.

The same scheme contains the unit: a morphism `e : Spec K ⟶ Y`
composes with `i` to the actual unit section of `A`. Actual inversion
restricts to a scheme automorphism of `Y`. For every actual rational
section of `A` whose image point belongs to the closure, its right
translation also restricts to a scheme automorphism of `Y`. Both
restrictions are specified by their commuting equations with `i`.
These assertions retain all the structural data of the published
`TwoPowerTorsionReducedClosureStatement` on the same witness `Y, i`.
Here reducedness is replaced by smoothness of the structure morphism;
over the field, smoothness implies reducedness.

Algebraic closedness is essential to the proposed argument, whereas
characteristic zero is not a hypothesis of this proposition. There is
no numerical torsion formula or group-object structure assumed or
asserted on `Y`. The proposition does not supply multiplication on
`Y`, a dimension comparison, or torsion density.

This file defines an internal derived prerequisite and gives no proof.
Its provenance is the published reduced-closure statement together with
the geometric principle extracted in
`Langlands.AlgebraicGeometry.ClosedPointHomogeneousSmoothStatement`.
The latter comes from Andrew Yang's private
`smooth_of_grpObj_of_isAlgClosed` in the registered source
`mathlib-group-smooth-5ed296525643`,
`Mathlib/AlgebraicGeometry/Group/Smooth.lean`, lines 28–61, pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`, SHA256
`4b78d0cacf95758052e21397c90cec6d556c443e38295ccd9ec4e6362c99bb6e`
(Apache 2.0). The full source was read and no corresponding project
errata note was found. The intended derivation uses rational sections
representing the closed points of `Y` and the restricted translations
to make `Y` homogeneous on closed points, then applies that geometric
smoothness principle. The original group-scheme lemma is not being
applied to `Y` before a group structure exists.
