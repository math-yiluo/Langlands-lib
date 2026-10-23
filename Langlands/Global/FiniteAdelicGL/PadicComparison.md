# Canonical p-adic and completion models of a finite local GL factor

This internal comparison connects the actual finite-completion model used by
finite adelic matrices with the canonical p-adic model used by local smooth
representations. The number field `K : Type u` is arbitrary, with its existing
`Field` and `NumberField` instances, and `v : FinitePlace K` is an actual finite
place. The p-adic field is `CompletionPadic.padicField v`, over the rational
residue prime below `v`. Its carrier is the same completed field
`FiniteCompletion K v`; no field isomorphism or local representation is chosen.

## Topology and integral subgroup

`localGL_topology_eq K v n` identifies the topology on `FiniteLocalGL K n v`
with `(CompletionPadic.padicField v).canonicalGeneralLinearTopology n` for
every natural rank `n`, including zero. Both general linear groups use matrix
units and the topology induced by the matrix and its inverse. The proof unfolds
the canonical matrix topology and applies the published equality
`CompletionPadic.completion_topology_eq` on the coefficient field. The remaining
matrix-unit topology equality is definitional.

`mem_localIntegers_iff_canonical K v x` identifies membership in the completed
integer ring `v.adicCompletionIntegers K` with membership in
`(CompletionPadic.padicField v).canonicalTopologicalData.Integers`. It composes
the published characterization of completed integers by canonical norm at most
one with the canonical p-adic integer-ring characterization by the same bound.
It asserts membership equivalence on the shared carrier, with no new valuation
normalization.

`localIntegral_eq_sphericalSubgroup K v r` then identifies the underlying
subgroup of `localIntegral K (r + 1) v` with
`Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r`. Both are
exactly matrices whose entries and inverse entries are integral. The proof
uses the two membership descriptions and the preceding integer-ring comparison.
The positive rank `r + 1` follows the existing spherical API.

## Continuous local inclusion

`localPadicInclusion K v n` is a continuous monoid homomorphism from
`GeneralLinear n (CompletionPadic.padicField v).Carrier`, equipped explicitly
with its canonical topology, to `FiniteAdelicGL K n` with its usual finite
adele topology. Its underlying monoid homomorphism is exactly
`localInclusion K n v`: it inserts the supplied matrix at `v` and the identity
matrix at every other finite place. The continuity proof transports the
existing inclusion's continuity along `localGL_topology_eq`; it does not change
the function or its multiplication laws.

The accompanying intrinsic proofs establish:

- `localPadicInclusion_apply`: equality with the original local inclusion on
  every matrix;
- `localPadicInclusion_injective`: injectivity inherited from that inclusion;
- `localProjection_localPadicInclusion`: projection at `v` is a left inverse;
- `comap_standardIntegral_localPadicInclusion`: the inverse image of the
  standard finite integral subgroup is exactly the canonical spherical
  subgroup in positive rank.

The last equality combines the existing inverse-image formula for
`localInclusion` with `localIntegral_eq_sphericalSubgroup`. The explicit domain
topology on the continuous homomorphism and its monoid-homomorphism projection
avoids relying on the two equal topologies being definitionally equal.

## Internal provenance and scope

This is an intrinsic comparison of published project constructions, not a new
translation of a literature theorem. Its inputs are
`Langlands.Global.FiniteAdelicGL.LocalFactor`,
`Langlands.Global.CompletionPadic`,
`Langlands.Correspondence.UnramifiedNormalization`, and
`Langlands.LocalField.Normalization.Proof`. It uses their actual completion,
canonical p-adic field, integral matrix subgroup and local inclusion, preserving
the original normalizations. The proof routes are precisely topology transport,
entrywise integer membership and the published inclusion identities described
above. No classification, Satake parameter, automorphic irreducibility or
restricted tensor factorization is asserted or assumed by this module.
