# Finite support on the second projection of an abelian square

This module proves
`Langlands.AbelianScheme.squareSecondProjectionSupport :
SquareSecondProjectionSupportStatement.{u}`.
The complete theorem type is the named proposition, with no extra outer
parameters or proof inputs.
For an abelian scheme `A` over an algebraically closed field `K`, let
`a := A.X.hom`, `Z := pullback a a`, and `p2 := pullback.snd a a`.
Let `Q` be an actual line bundle on `Z`, and let `F` be a finite set of
actual `K`-rational points of `A`. Suppose the cohomology of the restriction
of `Q` to `A × {x}` is zero in every natural degree whenever `x ∉ F`.
Then, for every `n : ℕ`, the actual scheme module
`(DerivedSections.higherDirectImage p2 n).obj Q.obj` has finite closed
support in the sense of the published `ModuleSupport` interface.

The coefficient in the hypothesis is exactly the underlying module of
`(LineBundle.pullback (squareSecondInclusion a x.left x.w)).obj Q`.
The inclusion is the pullback lift with components
`(𝟙 A.X.left, a ≫ x.left)`; the equation `x.w` makes `x` a section.
`HasFiniteClosedSupport` means that the locus of nonzero underlying
abelian-group stalks is finite and each of its points is closed.

## Implemented proof

Take `U := rationalPointComplement a F hF`, the open complement of the
underlying points of `F`. A rational point `y` of `U` over `Spec K`
defines the over-morphism `x` whose underlying map is `y ≫ U.ι`.
The subtype membership of its underlying point and
`mem_rationalPointComplement_iff` imply `x ∉ F`.
The hypothesis thus gives cohomology vanishing on the section inclusion.
`squareSecondFibreCohomologyIso` transfers it to the actual scheme fibre
`pullback p2 (y ≫ U.ι)`, with the ordinary module pullback of `Q.obj`.

Apply the published theorem
`DerivedSections.isZero_pullback_higherDirectImage_of_rationalFibres`
to this open and these fibre vanishings. Its universal-perfect-sections
premise is discharged by the published proof `universalPerfectSections`
from `UniversalPerfectSectionsProof`. Smoothness and properness of `p2`
follow from the corresponding properties of the abelian scheme's structure
map and their stability under base change. Local finite type of `a` also
comes from the abelian scheme. These instances are inferred in Lean.
Consequently, every higher direct image pulls back to zero on `U`.

Finally,
`hasFiniteClosedSupport_of_isZero_rationalPointComplement` gives finite
closed support from that zero pullback. Its support container is the
finite set of underlying points of `F`; its closedness uses the
algebraically closed field and local finite type already present here.

## Provenance and scope

This is an internal deduction from the named published interfaces.
It specializes the open-local rational-fibre vanishing result to the
second projection and composes it with the published support adapter.
It introduces no additional assertion from external literature.
Both degree quantifiers include zero, and the common universe `u` is
arbitrary. There is no characteristic or positive-dimension restriction,
and `F` may be empty. The theorem adds no coherence hypothesis.

This result supplies the finite-support step for
`AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement`.
It does not prove finite-support acyclicity or zero detection, Leray,
or reverse affine base change. Those proofs, followed by the total
cohomology argument, remain necessary for the complete detection theorem.
