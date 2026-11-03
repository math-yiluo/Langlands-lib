# Lie dimension decrease from a nontrivial connected kernel

Author: Worker 1478.

This internal helper supplies the strict decrease needed for dimension induction
through a supplied affine group quotient by a nontrivial split ground-field
unipotent radical. All declarations work over every field `k : Type u`, at
arbitrary universe `u`. Lie dimension is the existing `Lie.dimension`, the
finite dimension of the actual dual-number identity kernel.

`Lie.exists_tangent_ne_zero_of_range_ne_bot` considers any homomorphism
`n : N → G` whose source is connected, affine and locally of finite type.
If its subgroup-functor range differs from the bottom subgroup on all relative
tests, then the actual Lie kernel of `N` contains a nonzero vector. The proof
argues by contradiction: if every additive tangent vector is zero, the
multiplicative Lie kernel is a subsingleton. The published zero-tangent
triviality theorem makes every point of `N` on every relative scheme the
identity. Consequently the range of `n` is bottom, contradicting the premise.
No smoothness or monicity is needed for this first assertion.

`Lie.nonzeroTangentOfRangeNeBot` packages this existence result as actual
chosen tangent data: the subtype of additive vectors of `lieKernel N k`
which differ from zero. It has precisely the preceding lemma's hypotheses.
Classical choice supplies the vector, and its choice specification supplies
the nonzero proof. This is a noncomputable internal construction; no
canonical choice or extra property of the selected vector is asserted.

`Lie.dimension_lt_of_smooth_kills_connected_subgroup` takes a smooth
homomorphism `q : G → Q` between affine group schemes locally of finite type,
and a monomorphic homomorphism `n : N → G` with the preceding source
properties and nontrivial all-test range. The actual scheme-morphism equation
`n.hom.hom ≫ q.hom.hom = 1` says that `q` kills that subgroup. The first
construction gives a nonzero tangent vector of `N`; injectivity of the tangent map
of `n` preserves its nonzeroness in `G`. The killing equation makes its image
under the tangent map of `q` zero. The published smooth-differential dimension
lemma then proves `Lie.dimension Q < Lie.dimension G`. The argument imposes
no connectedness premise on `G` or `Q`.

`RelativeRoot.IsFppfQuotient.lieDimension_lt_of_nontrivial_connected_kernel`
applies this result to any supplied quasi-compact fppf group quotient whose
specified subgroup functor has a smooth connected affine representative `N`
locally of finite type and is not bottom. The existing represented-kernel
smoothness theorem proves that the supplied projection is smooth. Its exact
scheme-kernel equality gives the killing equation by testing on `N` and its
inclusion itself. Representability supplies monicity. Thus the full kernel,
rather than its rational or geometric points, provides the strict decrease.

Finally, `IsSplitUnipotentRadical.quotient_lieDimension_lt` specializes to a
supplied fppf quotient by a represented split ground-field unipotent radical
with nontrivial range. The ambient and quotient groups are assumed affine
and locally of finite type. The radical predicate gives smoothness,
connectedness and closedness of its source; closedness in the affine ambient
group gives affineness. The projection is quasi-compact because its composite
with the quotient structure map equals the affine structure map of the
ambient group. Applying the preceding theorem proves strict Lie-dimension
decrease, with no separate smoothness or quasi-compactness premise on the
projection.

The provenance is internal: these deductions combine the existing zero-tangent
triviality, tangent-map injectivity, smooth-differential dimension decrease,
represented smooth-kernel quotient theorem and affine-morphism properties.
They provide an induction step for the split-radical reduction. They do not
construct a group quotient or its pseudo-parabolic subgroup, establish torsor
triviality, or prove the unrestricted rational-lifting statement. No
perfectness, infinitude, characteristic or reductivity restriction is imposed.
