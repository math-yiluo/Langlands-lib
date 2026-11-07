# The canonical full function-field adelic tensor equivalence

For fields `k`, `K`, and `L` in an arbitrary common universe, assume that `k`
is finite, that `K` is a function field over `k` with its given rational-function
presentation, and that `L/K` is finite dimensional. The `k`-algebra structures
on `K` and `L` must agree through `K → L`. No separability hypothesis on
`L/K` is imposed.

`curvePlaceAdeleTensorEquiv k K L` constructs the `L`-algebra equivalence

`L ⊗[K] CurvePlaceAdeleRing k K ≃ₐ[L] CurvePlaceAdeleRing k L`.

Both rings are the actual restricted products of the completions at all
nontrivial discrete curve places trivial on `k`, with their completed valuation
subrings. The upper rational-function action is the composite
`RatFunc k → K → L`; its scalar towers and the function-field finiteness of `L`
are derived internally. Thus only the lower presentation is an input.

The underlying algebra homomorphism is exactly the previously constructed
`curvePlaceAdeleTensorMap`. The supporting theorem
`curvePlaceAdeleTensorMap_bijective` proves its bijectivity. The
`curvePlaceAdeleTensorEquiv_toAlgHom` identity and
`curvePlaceAdeleTensorEquiv_tmul` formula record that the equivalence sends
`a ⊗ x` to the principal adele of `a` times the original adele inclusion of `x`.
In particular, it uses the original completed embedding at every upper place.

The proof first identifies points of the actual affine-chart Weil restriction
on a test ring `R` with actual affine-line points over `L ⊗[K] R`.
Naturality of the spectrum pullback identifies change of coefficients along a
compatible tensor map with the original Weil counit evaluation. Polynomial
evaluation identifies affine-line points with their coefficients, and this
identification commutes with every algebra homomorphism. These are internal
generic lemmas; together they transfer bijectivity of affine-line evaluation
to bijectivity of the literal coefficient map.

For the adelic specialization, the affine line is given its standard open
immersion into projective one-space. The function-field projective model is
constructed internally using the image of `RatFunc.X` in `K`, starting with
empty initial exceptional supports. The published model constructor chooses
its necessary denominator and exceptional set. The published adelic Weil
homeomorphism and its counit identity give bijectivity of the original affine-line
evaluation. Its two endpoint topologies are the already constructed spread
topologies. Equality of the original affine-line presentation with the polynomial
spectrum transports the evaluation and its dependent finite-type instance.
The generic coefficient argument then proves tensor-map bijectivity, and
`AlgEquiv.ofBijective` packages that same algebra homomorphism.

This is a derived arithmetic construction from Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 4.2,
printed pp.9–10, registered as
`conrad-2011-weil-grothendieck-adelic-points` (PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).
The natural equality of adelic Weil point sets on p.10, applied to the affine
line, yields precisely this arithmetic tensor identity. The explicit tensor-map
comparison and algebra-equivalence packaging are derived content.

This unit asserts an algebra equivalence. It does not specify a tensor-product
topology, prove the separate algebraic-space comparison, or complete the
whole-paper formalization.
