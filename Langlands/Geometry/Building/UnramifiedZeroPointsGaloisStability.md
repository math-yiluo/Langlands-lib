# Galois stability of the unramified zero subgroup

This derived module proves clause 2 of
`Langlands.Geometry.Building.UnramifiedZeroDescentStatement`: for every
nonarchimedean local field `F : Type u`, every group scheme `G` over `F`,
every supplied `UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G)`,
every `F`-automorphism `σ` of the maximal unramified extension, and every
`x ∈ E.zeroPoints`, the conjugate of `x` belongs to `E.zeroPoints`.
No additional connected reductivity premise is needed because the supplied
datum contains the required structural hypotheses.

The simply connected image argument applies over arbitrary field extensions
`K/k`, for a group scheme defined over `k` and any supplied derived cover over
`K`. `baseChange_comp_iso_isSimplyConnectedDerivedCover` transports that cover
along a field-spectrum isomorphism and an ambient isomorphism.
`rationalConjugate_mem_conjugate_range` transports rational range membership
using the published subgroup-functor conjugation comparison and range
transport formula. `baseChange_comp_range_eq_simplyConnectedImage` identifies
the transported range with any supplied simply connected image in the target.
`rationalConjugate_mem_simplyConnectedImage` combines these results for the
coefficient automorphism and canonical ambient descent isomorphism.

`UnramifiedZeroDatum.rationalConjugate_mem_zeroPoints` uses the defining join
of the simply connected image and the image of `E.torusIwahori`. It proves
that this join is contained in its preimage under the conjugation
homomorphism. On the first summand it applies the simply connected image
stability lemma. On the second it represents a point by an element of
`E.torusIwahori` and applies the existing
`rationalConjugate_torusIwahori_mem_zeroPoints`, which uses transport of the
torus norm subgroup and independence of the zero datum.

`UnramifiedZeroPointsGaloisStabilityStatement` is a Prop-valued packaging of
exactly this unconditional pointwise result. Its provenance is internal and
derived from the named Library constructions, cover independence, range
transport, and the torus lemma
`rationalConjugate_torusIwahori_mem_zeroPoints`. No new original
literature interpretation is made. The module proves no descent comparison
with `G(F)` and does not by itself prove the full three-clause target.
