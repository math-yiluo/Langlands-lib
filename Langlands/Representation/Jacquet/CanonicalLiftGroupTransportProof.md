# Canonical Jacquet lift transport through group equivalences: proof

Author: Worker 127.

`Langlands.Jacquet.canonicalLiftGroupTransport` proves exactly the published
`Langlands.Jacquet.CanonicalLiftGroupTransportStatement`. Its full telescope has
independent universes for `G`, `H`, and `V`, with the group, topology, topological
group, additive group, and complex module instances of the statement. It adds no
hypotheses. The four clauses are proved in their published order: normalized
average equality, stable-image membership equivalence, generalized-kernel equality
iff, and bijectivity iff of the actual stable-image Jacquet map.

This is derived internal functoriality of the definitions imported by
`Langlands.Representation.Jacquet.CanonicalLiftGroupTransportStatement`, not a
claim quoted from external literature. The proof uses the existing
`fixedVectors_comp_mulEquiv`, `coinvariantsMapEquiv`, and
`coinvariantsMapEquiv_mk`. Smoothness is pulled back by `isSmooth_comp`.
Admissibility, finite dimension, stabilization, and either canonical-lift
conclusion are not assumed. The existing admissibility transport theorem remains
available from the imported `CuspidalSupport.GroupTransport` module but is not
needed in this proof.

## Actual averaging and fixed-vector spaces

For a continuous group equivalence `e : H ≃ₜ* G`, the source representation is
`ρ.comp e.toMonoidHom` on the same `V`. The compact open subgroups satisfy the
actual image equality `K.toSubgroup.map e.toMonoidHom = L.toSubgroup`.

`orbit_groupTransport` proves equality of the two subgroup orbits as sets of
vectors. A source orbit representative maps to its image under `e`; a target
representative has a preimage in `K` by the image equality.
`averageMap_groupTransport` then unfolds `orbitMean`. Both its `Nat.card` factor
and its finite-support sum are expressions in that same orbit set, so rewriting
the orbit equality proves equality of the normalized linear endomorphisms of
`V`. `averageMap_groupTransport_apply` evaluates this equality on **every** vector
`v : V`, with no fixedness hypothesis. It can therefore be used at a larger
compact subgroup on a vector fixed by a smaller subgroup.

`fixedVectors_groupTransport` rewrites the existing pullback fixed-vector theorem
and identifies inverse comap with forward image. The equivalence
`fixedVectorsGroupTransportEquiv` is `LinearEquiv.ofEq` for this equality of
submodules. Its evaluation law is the identity on underlying vectors.

## Compressed actions, powers, and stable images

`compressedAction_groupTransport` proves pointwise conjugacy by applying the
average identity to `ρ (e g) v`. `compressedAction_pow_groupTransport` extends
this by induction to every natural power, including zero.

`mem_stableImage_groupTransport` uses the existing characterization of stable
membership as membership in every power range. It transports a preimage witness
by the fixed-vector equivalence; the reverse direction uses that equivalence's
surjectivity and injectivity. `stableImage_groupTransport` is the published
same-ambient-vector formulation with the two fixedness proofs.

`stableImageGroupTransportEquiv` restricts the fixed-vector equivalence to these
actual stable-image submodules. The theorem
`stableImageToRepresentation_groupTransport` states that the transported vector
has exactly the same pointwise image in `V` through the existing inclusion map.
This equivalence makes no stabilization or invertibility assertion about the
compressed operator.

`powerKernelSup_map_groupTransport` transports the actual supremum of the
kernels of all compressed powers. The implementation distributes submodule
mapping over the supremum and proves equality of each mapped kernel using power
conjugacy, injectivity, surjectivity, and preservation of zero. No assertion that
this supremum eventually stabilizes is used.

## The unnormalized action and actual Jacquet codomains

For subgroups `N, M` and `N', M'`, the proof uses the supplied normalizer
inclusions and image equalities for `N` and `M`.
`coinvariantsGroupTransportEquiv` is the existing `coinvariantsMapEquiv`, with
its target rewritten using `N.map e.toMonoidHom = N'`. Its `mk` law sends the
class of `v` to the class of the same `v`.

`action_groupTransport` proves equivariance for the actual unnormalized
descended actions. It allows any `m : M` and `m' : M'` with `e m = m'`.
Surjectivity of `mk` reduces the assertion to a representative in `V`, where
`action_mk` and the coinvariant evaluation law give it directly.

`fixedJacquet_mem_groupTransport` identifies the fixed spaces for precisely
`K.toSubgroup.comap M.subtype` and `L.toSubgroup.comap M'.subtype`. In the forward
direction, a target element in `M'` has a preimage in `M`; its membership in `L`
and injectivity of `e` place that same preimage in `K`. The reverse direction
maps an element of `K ∩ M` directly into `L ∩ M'`. Action equivariance then
transfers fixedness in both directions.

`fixedJacquetGroupTransportEquiv` restricts the quotient equivalence to these
actual fixed codomains. `fixedJacquetGroupTransportEquiv_apply` records its
pointwise evaluation through the quotient equivalence.
`fixedJacquetMap_groupTransport` and `stableImageJacquetMap_groupTransport`
prove commuting-square identities for the existing restricted quotient maps.
Their proofs reduce by subtype extensionality to the same `mk` evaluation law.
Thus neither the quotient maps nor their codomains are replaced by abstract
surrogates.

## The two conclusion equivalences

`fixedJacquetMap_ker_map_groupTransport` maps the actual restricted quotient
kernel to the corresponding target kernel, using its commuting square.
`powerKernelSup_eq_ker_groupTransport` combines this with the transported power
kernel supremum. The forward direction maps the equality; the reverse uses
injectivity of submodule mapping under the fixed-vector equivalence.

`stableImageJacquetMap_bijective_groupTransport` uses the stable-domain and
fixed-codomain equivalences and the commuting square to transport injectivity
and surjectivity in both directions. Its two sides are exactly bijectivity of
the existing `stableImageJacquetMap` constructions. No bijectivity is assumed
except locally as the antecedent of the relevant implication.

The closing theorem bundles the four named consequences. The module adds only
four equivalences of existing carriers and proved transport results. It proves
neither an opposite canonical-lift theorem nor a pairing theorem. The closing
proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
