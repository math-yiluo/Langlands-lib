# Totally disconnected quotients of topological groups

Module `Nyll.GaloisCohomology.Topology.TotallyDisconnectedQuotients`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves two ways of producing totally disconnected quotients of a topological group: dividing a profinite group by a closed normal subgroup, and dividing any topological group by the connected component of the identity.

- `QuotientGroup.totallyDisconnectedSpace_of_isClosed`: if `G` is compact, Hausdorff and totally disconnected and `N` is a closed normal subgroup, then `G/N` is totally disconnected.
- `QuotientGroup.Subgroup.Normal.connectedComponentOfOne`: an instance stating that the identity component of a topological group is normal.
- `QuotientGroup.totallyDisconnectedSpace_quotient_connectedComponentOfOne`: for any topological group `G`, the quotient of `G` by its identity component is totally disconnected.
- `ContinuousMonoidHom.connectedComponentOfOne_le_ker`: a continuous homomorphism into a totally disconnected topological group kills the identity component.

## Proofs

For the first result, two distinct classes `xN ≠ yN` are separated by a clopen set: since `N` is closed, an open normal subgroup `V` can be chosen (by `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`) so that `x⁻¹y ∉ NV`; the image of the open subgroup `NV` in `G/N` is open, hence clopen, and a translate of it separates the two points. Thus `G/N` is totally separated. For the second, the fibres of the quotient map are translates of the identity component, hence connected, so the preimage of the identity component of the quotient is the identity component of `G`.

## Points to watch

- The instance name `QuotientGroup.Subgroup.Normal.connectedComponentOfOne` lives in the namespace `QuotientGroup`, not `Subgroup`.
- The second quotient result needs no compactness or separation hypothesis on `G`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Topology/TotallyDisconnectedQuotients.lean`: the Lean file is the source byte for byte (SHA-256 `176f8dc71dfffe4b3253b1594642f8d4fe85f8734c2855b858656ad6cd588834`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
