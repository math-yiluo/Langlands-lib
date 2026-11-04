# Lifting adjoint differences through a central isogeny

This internal construction applies the published
`CentralIsogeny.CommutatorDescent` to actual dual-number points. Let
`q : G ⟶ H` be a group-scheme homomorphism over the spectrum of an arbitrary
commutative ring `R`, with central full scheme-theoretic kernel and a
quasi-compact, flat, surjective underlying morphism. These hypotheses
permit the published commutator descent. Every central isogeny satisfies them.

For any commutative `R`-algebra `A`, a point `n ∈ G(A)` and an actual
identity-kernel point `X ∈ Lie H(A)`,
`CommutatorDescent.tangentLift q hq n X` evaluates the descended
commutator on the pair consisting of the constant dual-number point
`q(n)` and `X`. This gives an actual point of `G(A[ε])`. Reduction sends
the input pair to `(q(n), 1)`. The published lifted-point formula identifies
its output with the commutator `[n, 1] = 1`, proving that the output lies
in the original identity kernel `lieKernel G A`.

`targetMap_tangentLift` applies the published `hom_comp` identity to the
pair. It proves the exact identity on original kernel points:

```
dq(tangentLift(n, X)) = Ad(q(n))(X) * X⁻¹.
```

Here the product and inverse are those of the actual identity kernel.
When both groups are affine, this kernel is the published additive Lie
module, with scalar multiplication given by epsilon scaling.
`targetMapLinear_tangentLift` then expresses the same identity as
`dq(tangentLift(n, X)) = Ad(q(n))(X) - X`.
Consequently `range_adjoint_sub_id_le` proves that the range of every
linear operator `Ad(q(n)) - id` is contained in the range of the actual
linear differential of `q`.
`range_adjoint_sub_id_le_of_centralIsogeny` specializes this containment
to the published central-isogeny predicate, discharging the three
morphism hypotheses from that predicate.

The proof uses no smoothness, finite-type condition on the groups, field
assumption, separability or restriction on the characteristic. It makes
no linearity assertion about the two-variable construction `tangentLift`.
It does not yet prove surjectivity on nonzero weight spaces, equality
of roots or the central-isogeny root-datum statement. Those require
further weight and character arguments.

The provenance is internal: the only descent input is the published
actual commutator morphism and its factorization. All tangent and adjoint
identifications use the published actual dual-number identity kernels.
