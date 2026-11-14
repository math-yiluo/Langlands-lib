# Injectivity of the actual degree-two sum map

This is an internal construction in
`Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq`.
Write \(H^n(X)\) for the actual right-derived structure-sheaf cohomology
`(relativeCohomology X.hom n).obj (unitModule X.left)`.

## Pullback laws and affine-base vanishing

For any commutative ring `R`, `unitCohomologyPullback_id` and
`unitCohomologyPullback_comp` establish the identity and contravariant
composition laws for the canonical unit-module pullback. The proofs use
relative-cohomology pullback identity and composition, together with the
corresponding laws for the unit-module comparison isomorphism.

For a point `e : Spec R → Y` over `Spec R`,
`unitCohomologyPullback_to_base` proves that the induced map on every
positive-degree cohomology group is zero. The target is zero by the published
affine quasicoherent cohomology vanishing theorem, applied to the unit module
of `Spec R`. The categorical zero-object property gives equality of the
underlying linear maps. Consequently `unitCohomologyPullback_base` proves
vanishing for every map `X → Spec R → Y` in positive degrees.

Suppose `P` has maps `p₁ : P → X`, `p₂ : P → Y`, points on `X` and `Y`, and
axis maps `iX : X → P`, `iY : Y → P`. Assume each axis followed by its own
projection is the identity and followed by the other projection factors
through the specified point. Then `axisPullbacks_eq_zero` proves
\[
p_1^*x+p_2^*y=0\quad\Longrightarrow\quad x=y=0
\]
in every positive degree. Apply each axis pullback, use composition,
and eliminate its cross term by affine-base vanishing. This part does not
require a field or a fibre-product hypothesis.

## The actual degree-two sum

Over a field `K`, for schemes `X`, `Y`, `P` over `Spec K`, define the linear map
\[
\Phi:H^2(X)\times\bigl(H^1(X)\otimes_K H^1(Y)\bigr)\times H^2(Y)
  \longrightarrow H^2(P),\qquad
\Phi(x,t,y)=p_1^*x+\operatorname{mixedTensor}(t)+p_2^*y.
\]
This is `degreeTwoSum`. The product is right associated in Lean.
`mixedTensor` is the actual mixed cup from `AllSeqMixedSlant`, in the order
first-axis pullback followed by second-axis pullback, using `cupCanonical`
on the specified product cover. Thus this construction is a particular map
on actual cohomology, with its mixed term determined by the existing cup.
Linearity follows from the three summands' linearity and distributivity.

The map itself requires finite index types `ι`, `κ` in the field's universe,
families `U : ι → X.Opens`, `V : κ → Y.Opens`, separatedness of `P`, and
covering and affine-member hypotheses for the family `prodCover p₁ p₂ U V`
on `P`.

For detection and injectivity, the retained additional assumptions are:

- the underlying projection square is an actual `IsPullback` over `Spec K`;
- the structure morphisms of `X` and `Y` are separated as well;
- on every open of `X`, `Y`, and `P`, the supplied section-algebra map equals
  the map induced by its structure morphism (`halgX`, `halgY`, `halgP`);
- `U` and `V` cover their schemes and have affine members;
- every two-entry `U` intersection and every nonempty finite `V` intersection
  is affine, as required by the existing shuffle-slant construction.

## Detection and injectivity

`mixedTensor_eq_zero_of_degreeTwoSum` proves that `Φ(x,t,y)=0` implies `t=0`.
Choose a basis of the vector space `H¹(X)`. Apply shuffle slant by each basis
coordinate functional to the equality. The two axis terms vanish by
`slantByH1Dual_pull_left` and `slantByH1Dual_pull_right`, which apply to
arbitrary degree-two axis classes. The mixed term contracts by
`slantByH1Dual_mixedTensor`. Each resulting equation says a coefficient of
`t` is zero. Mathlib's `TensorProduct.equivFinsuppOfBasisLeft` identifies
these contractions with all coefficients, so the tensor vanishes.
Finite dimensionality is not assumed.

`degreeTwoSum_injective` adds points and axis maps satisfying the four
composition laws above. In the kernel, mixed detection first removes `t`;
`axisPullbacks_eq_zero` then removes `x` and `y`. The zero-kernel criterion
proves injectivity.

`degreeTwoSum_injective_of_points` requires only the two points in addition
to the stated detection hypotheses. The universal property of the actual
pullback constructs the axis maps from the identity on one factor and the
constant map on the other. Their projection equations are exactly the
four laws used by `degreeTwoSum_injective`.

## Provenance and remaining scope

All new results are internal derivations from published or included actual
pullback, cup, shuffle-slant, arbitrary-axis vanishing and affine-cohomology
interfaces, plus elementary linear algebra and the pullback universal
property. The geometric maps and cohomology objects are actual schemes and
right-derived unit-module cohomology. No arbitrary Kunneth equivalence or
exterior-generation premise is used. There is no characteristic restriction.

This unit proves injectivity under the explicit cover and point hypotheses.
It does not prove surjectivity, cover independence of the mixed cup,
creation-contraction identities, alternation, exterior generation, or the
host exterior and canonical coproduct comparison.
