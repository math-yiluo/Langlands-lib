# Actual tangent differentiation on finite-smooth adelic functions

This internal construction combines actual infinite tangent differentiation with
finite-level slice reconstruction. It adapts the descent in the public
`Langlands.Automorphic.EnvelopingAction` to first-order actual group-scheme
differentiation. Worker 94 supplies this adaptation; Worker 72's reconstruction
and descent arguments are retained. Its base is any number field `F : Type u`
and any affine group scheme `G` over `Spec F` with the explicit algebraic
premise `SmoothOfRelativeDimension d G.X.hom`. No splitness or positive rank is
assumed.

`differentiatePlotSliceFamily hsmooth L X` applies the previously constructed
`plotSmoothDifferential hsmooth X` to each infinite slice. This is the actual
real derivative at the identity of `h ↦ f(g * h)`, with positive right
multiplication, acting complex linearly on the original plot-smooth carrier.
Equality of slices at `b * l` and `b` proves retention of the same specified
open finite stabilizer. Rational covariance is first expressed as an equality
under actual infinite left pullback. The proved commutation of differentiation
with that pullback then proves covariance of the differentiated family. Thus
neither covariance nor derivative closure is supplied as an extra premise.

`finitePlotSmoothDifferential` chooses one of the input function's existing
common open finite stabilizers, extracts its actual slices, differentiates and
reconstructs. The result belongs to the unchanged
`FinitePlotSmoothRationalFunctions`. The reconstruction theorem proves joint
continuity, rational-left-invariance, plot smoothness and a common open finite
stabilizer. In particular this is an actual function on the original adelic
point group, rather than an abstract family.

`finitePlotSmoothSlice_differential` characterizes every output slice by the
original infinite tangent derivative. Faithfulness of slice extraction proves
`finitePlotSmoothDifferential_eq_reconstruct`: any specified open finite
stabilizer fixing the same input yields the identical output function.
The same slice characterization proves complex linearity on functions in
`finitePlotSmoothDifferentialAction`, and real linearity in the actual identity
tangent in `realFinitePlotSmoothDifferential`. The evaluation theorem exposes
the manifold derivative of the original function on
`pair (a * h) b` at `h = 1`. Its actual tangent and atlas are the ones previously
constructed from `hsmooth`.

The original finite positive right action simply changes slice index `b` to
`b * c`. It therefore commutes with this differential. As a consequence every
finite subgroup fixing the original function fixes its derivative; this
preservation theorem does not require that specified subgroup to be open or
compact. The separate theorem for `HasFiniteLevel` retains exactly the same
compact open subgroup when one is present. No existence of a compact open
subgroup is asserted or needed for the open-stabilizer construction.

`reductiveRealFinitePlotSmoothDifferential` uses the previously proved
constant-relative-dimension result for the original connected-reductive
predicate and its specified reductive atlas. Its tangent action requires no
extra analytic smoothness or chosen dimension premise. The ambient affineness
instance remains explicit in this file and follows from connected reductivity
by the existing `affineScheme` theorem.

This unit constructs first-order tangent differentiation and its intrinsic
descent laws. It does not assert a Lie-bracket law, construct a general
universal enveloping action, identify derivatives of exponential curves,
establish any derivative growth bound, or construct quotient measures or
cuspidal `L2` realizations. The existing general-linear differential comparison
is available for a further finite-smooth specialization.
