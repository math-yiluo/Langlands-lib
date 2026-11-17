# The actual generic closure isomorphism over a DVR

This is an internal derived construction from the actual generic-subgroup
closure and factorization, the smooth-target generic-closure construction,
and `EtaleOpenGenericIsomorphism.isIso_of_dvr`. It also specializes the result
to general linear groups using their published smoothness theorem. No
external-source translation is asserted. The universe `u` is arbitrary.

The generic section works over a Dedekind domain `R` with a specified
fraction field `K`. Its source `M` is flat, affine and locally of finite
type over `Spec R`; its target `G` is smooth and affine. The homomorphism
`f : M ⟶ G` is monic on underlying schemes. The imported construction
`closure (K := K) f` is the schematic closure of the actual generic image,
and `factor (K := K) f` is the canonical homomorphism to this closure. Its
composite with the closed `inclusion (K := K) f` is exactly `f`.

`genericFactor_isIso` identifies the generic base change of this factor
with the hom of `GenericSubgroupClosure.genericToClosureIso` using
`GenericSubgroupClosure.baseChange_factor` and the identity map on the
generic source. It follows that the actual generic factor is invertible.
Reductivity of `M` is not needed for this generic assertion.

The DVR section assumes an integral domain with
`IsDiscreteValuationRing R` and also assumes that `M` is reductive. The
flatness, affineness and finite-type structure hypotheses on the source
remain in the context used to form the closure; reductivity supplies
these when applying the result. The target remains smooth and affine,
and the original homomorphism remains monic. No generic-isomorphism
hypothesis on the original `f` is required.

For `factor_isIso_of_dvr`, the imported `closure_smooth` proves smoothness
of this actual generic closure, which is also affine by the closure
construction. The imported `factor_isOpenImmersion` proves openness of
the canonical factor from the reductive source. Together with
`genericFactor_isIso`, these are precisely the hypotheses of the
étale-descended DVR open-subgroup isomorphism criterion. Thus the
canonical factor itself is an isomorphism of group schemes.

`factorDvrIso` is the resulting actual isomorphism
`M ≅ closure (K := K) f`, defined as `asIso` of the canonical factor.
`factorDvrIso_hom` identifies its forward homomorphism with that factor.
`factorDvrIso_hom_inclusion` identifies its composite with the actual
closed closure inclusion with the original `f`; its reassociated form
is also a simplification lemma.

`isClosedImmersion_of_dvr` chooses `FractionRing R`, uses this factor
isomorphism and forgets it to the underlying schemes. The factorization
identity then expresses the original scheme morphism as an isomorphism
followed by a closed immersion, so the original map is a closed
immersion. The conclusion is about the actual given homomorphism.

Finally, `dvrMatrixCase` proves
`ReductiveDvrMatrixMonomorphismStatement.{u}`. For a monic representation
of a reductive `M` into `GL(Fin N)`, reductivity provides smoothness and
affineness of the source, and `GeneralLinear.smoothStatement` provides
smoothness of the affine general linear target. The preceding smooth
affine target theorem therefore applies.

These results do not assume a connected-fibre theorem or a supplied
split maximal torus. The target hypotheses in the smooth affine theorem
remain explicit. Reduction from a general separated finitely presented
target over a DVR, and the unrestricted arbitrary-base host theorem,
are separate obligations.
