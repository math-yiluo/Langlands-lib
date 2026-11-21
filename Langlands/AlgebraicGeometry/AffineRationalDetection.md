# Detection on rational slices, including after nonreduced base change

Let `K` be a field and let `R` and `B` be commutative `K`-algebras.
`tensorEvaluation e`, for `e : R →ₐ[K] K`, is the `K`-algebra map
`R ⊗[K] B →ₐ[K] B` taking `r ⊗ b` to `e(r) · b`. If a family of such
`e` has joint kernel zero, then the tensor evaluations have joint kernel
zero (`tensorEvaluations_separate`). The proof chooses a `K`-basis of `B`,
writes the tensor as a finitely supported family of coefficients in `R`,
and tests every coefficient by every `e`. In particular, `B` may contain
nilpotents. For a closed immersion into `Spec (R ⊗[K] B)`, if every
`Spec B` slice defined by a tensor evaluation factors through the closed
subscheme, its defining ideal on the affine target is zero and the
immersion is an isomorphism (`isIso_of_factors_tensorEvaluations`).

For a rational point `x : Spec K → X` and any scheme `T` over `K`,
`rationalSlice x T` is the map `T → X ×[K] T` with components the
constant map at `x` and the identity of `T`. Its projection and
naturality lemmas concern these actual maps in `Over (Spec K)`.

`hom_ext_of_rational_slices` assumes that `K` is algebraically closed,
`X` is reduced and locally of finite type over `K`, `U ⊆ X` is a dense
open, and `Y` is separated over `K`. It proves that two maps
`X ×[K] T → Y` over `K` are equal if they agree after `rationalSlice x T`
for every rational point `x` in `U`. The parameter scheme `T` is
arbitrary over `K`; in particular it need not be reduced or of finite type.

The proof works on products of affine open charts `Spec R` and `Spec B`.
If `r` is a nonzero element of `R`, reducedness makes its basic open
nonempty. The image of this basic open meets `U`, so the intersection
back in the chart contains a rational point by `ClosedRationalPoints`.
Its evaluation of `r` is nonzero. On the chart product, the affine
pullback isomorphism identifies the rational slices with the spectrum
maps of the tensor evaluations. The restricted maps have a closed
equalizer by separatedness. Every slice factors through it, so it is
the entire chart product as a scheme, not merely on underlying points.
Equality on the open cover gives equality of the maps.

This is an internal Library helper: it combines the rational-point
dictionary with the Mathlib affine pullback and tensor-basis interfaces.
Its intended application is equality for infinitesimal translation
parameters in the proof of cubic separation, where agreement on only
the underlying points of a product would not suffice.
