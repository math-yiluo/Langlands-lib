# Nonarchimedean topology on subgroups

`Langlands.subgroupNonarchimedean` gives every subgroup of a
nonarchimedean group the nonarchimedean property for its induced topology.
It requires a group, a topology and `NonarchimedeanGroup` on the ambient
type; there are no closedness, compactness or separation hypotheses.

A neighborhood of the subgroup identity comes from an ambient neighborhood.
Choose an ambient open subgroup inside that neighborhood, then take its
preimage under the subgroup inclusion. This is an open subgroup contained
in the original neighborhood.

The proof is moved unchanged from the private `subgroup_nonarchimedean`
helper in `Langlands.Weil.Local.AssemblyProof`. It also supplies the
instance previously defined as `Langlands.HaarModulus.subgroupNonarchimedean`
in the accepted Haar-modulus contribution. Both modules now import this
shared fact; their mathematical statements and hypotheses are unchanged.
