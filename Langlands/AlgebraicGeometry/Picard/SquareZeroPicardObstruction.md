# Actual Picard lifting over nonsplit square-zero immersions

This internal construction combines the published actual square-zero unit
cohomology sequence with the published additive Picard classifier and its
compatibility with actual scheme pullback. It adds no external source input.
All results hold for schemes `X` and `Y` in an arbitrary universe `u`, with
compact underlying spaces, and an actual closed immersion `i : Y ⟶ X`
with `i.ker ^ 2 = ⊥`. There is no splitting hypothesis.

Write `I = StructureKernelModule.kernelModule i`. The cohomology
`idealCohomology i n` is the underlying additive group of the actual
module-derived cohomology `(Modules.DerivedSections.cohomology X n).obj I`.
The maps are

```text
obstructionMap : Pic(Y) → H²(X,I)
  = boundaryMap₁ ∘ unitCohomologyAddEquiv(Y)

oneAddPicardMap : H¹(X,I) → Pic(X)
  = unitCohomologyAddEquiv(X)⁻¹ ∘ oneAddMap₁.
```

Here the Picard groups and their pullback are the existing groups of
isomorphism classes of actual tensor-invertible module sheaves and the
homomorphism induced by actual scheme-module pullback. The boundary and
`1+a` maps are those of `SquareZeroUnitCohomology`, constructed from the
actual short exact sequence of structure-unit sheaves on the small Zariski
sites. `cohomology_oneAddPicardMap` records the defining compatibility.

`oneAddPicardMap_range_iff` identifies the image of actual ideal-module H¹
with the kernel of actual Picard pullback. `picard_lift_iff` says that an
actual Picard class on `Y` lifts to `X` exactly when its defined obstruction
in actual H² vanishes. The proofs transport the published exactness
theorems through the additive classifiers, using
`Group.unitCohomologyClass_pullback_squareZero` to identify the intervening
map with actual Picard pullback.

`lineBundle_lift_iff` states the same obstruction criterion for an actual
locally free rank-one module sheaf on `Y`. A lift is an actual line bundle
on `X` whose pullback is isomorphic as a module sheaf to the prescribed
bundle. The proof passes between Picard classes and line bundles using
the published representative and class-equality criterion.

`same_pullback_iff` describes every nonempty fibre of Picard pullback as
the shifts of any chosen lift by `oneAddPicardMap`. The parameters need
not be unique: `oneAddPicardMap_eq_zero_iff` identifies the kernel with the
image of the actual boundary from unit-sheaf H⁰ on `Y`, and
`shifts_eq_iff` says that two parameters give the same shifted class
exactly when their difference is such a boundary. Thus the statements
retain the ambiguity coming from degree-zero units; they make no claim
that raw ideal-module H¹ acts freely.

The final two corollaries give surjectivity of Picard pullback when actual
ideal-module H² vanishes, and injectivity when actual ideal-module H¹
vanishes. All equalities concern ordinary Picard classes. The module does
not assert compatibility of these constructions under further base change,
coherence or finiteness of the kernel module, representability of the
lifting functor, or the final fppf Picard-sheaf representability target.
