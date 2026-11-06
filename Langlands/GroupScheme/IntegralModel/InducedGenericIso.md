# The generic comparison induced by an abstract integral isomorphism

This internal construction applies over any commutative domain `R` and any
fraction field `K`, with both in `Type u`. Let `M : IntegralModel R K G`
and `N : IntegralModel R K H` be actual supplied models. Starting with any
abstract integral group-scheme isomorphism `e : M.group ≅ N.group`, define

`inducedGenericIso M N e = M.genericIso.symm ≪≫ (baseChange (Spec.algebraMap R K)).mapIso e ≪≫ N.genericIso`.

Thus it first identifies the original group `G` with the actual generic
fibre of `M`, applies the actual base change of `e`, and then uses the
original supplied identification of the generic fibre of `N` with `H`.
All groups, models, coefficient maps and supplied generic identifications
are retained. No Henselian, reductivity, smoothness, or characteristic
hypothesis is required for this adapter.

`Iso.ofGroupIso` constructs an actual compatible `M.Iso N` over that
induced generic isomorphism. Its compatibility equation follows by
cancelling `M.genericIso.hom ≫ M.genericIso.inv`. Its `iso` field is
exactly `e`. Conversely, `Iso.inducedGenericIso_eq` shows that if an
integral isomorphism is already compatible with a prescribed generic
isomorphism `f`, the induced generic isomorphism equals `f`; this follows
by cancelling the same original generic identification in the compatibility
equation.

`map_integralPoints_inducedGenericIso` then proves equality of the actual
subgroup images:

`M.integralPoints.map (rationalPoints.map (inducedGenericIso M N e).hom) = N.integralPoints`.

The proof applies the published `Iso.map_integralPoints` to the constructed
compatible isomorphism. That imported theorem uses the actual equivalence
on integral sections and naturality of the original integral-point maps.
The final lemmas prove that induced generic isomorphisms preserve identity,
composition and inversion. The proofs expand their actual categorical
composites and cancel the intermediate supplied generic identifications.

The provenance is the internal combination of the published
`IntegralModel.Iso` compatibility record, coefficient base change,
and `Iso.map_integralPoints`; no original-literature assertion is added.
For `G = H`, the induced generic map is an actual automorphism of the
original generic group. An abstract integral isomorphism does not imply
that this automorphism is the identity or that the two original integral
images are equal without its action. This construction neither asserts
existence of an integral isomorphism nor constructs an action of the
induced generic automorphism on a building. Those remain separate inputs
to the supplied-model building-comparison route.
