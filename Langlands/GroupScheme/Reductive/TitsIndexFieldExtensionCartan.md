# Comparing an actual Tits-index Cartan matrix after splitting

Let `d` be actual Tits-index data of a group `G` over an arbitrary field `k`.
Let `L` be a field extension of `k` equipped with a compatible embedding into
`SeparableClosure k`. Suppose a split maximal torus `i : S → G_L` and an
actual integral root datum `P` of that torus are supplied.

`TitsIndexData.nonempty_rootDatumEquiv_of_split_maximalTorus` gives a full
root-datum equivalence from `P` to the absolute root datum stored in
`d.pinning`. No comparison of the distinguished vertices, anisotropic
vertices or Galois star actions is asserted.
`splitMaximalTorusRootDatumEquiv` chooses such a full equivalence by
classical choice.

The implemented proof pulls `P` back from `L` to the separable closure using
the actual character and cocharacter lattice equivalences. The maximal
torus remains maximal after extension. The canonical group isomorphism
between iterated and direct field extensions then permits the imported
comparison of root data on two split maximal tori of isomorphic connected
reductive groups. Composing with the actual lattice base-change equivalence
returns an equivalence from the original `P`.

`TitsIndexData.splitMaximalTorusBase` transports the specific base in
`d.pinning` along the inverse chosen full root-datum equivalence.
`splitMaximalTorusBaseEquiv` identifies `d.Vertex` with the support of this
defined base. The theorem `cartanMatrix_splitMaximalTorusBaseEquiv` proves
that this equivalence preserves every integer Cartan entry. Mathlib's
base-map Cartan formula
then gives the exact matrix comparison. The integral pairing in the Tits
index is the same integer pairing used by this Cartan formula.
`exists_base_cartanEquiv_of_split_maximalTorus` packages the defined base,
equivalence and entry equality as an existence theorem.

This is an internal composition of the imported field-extension,
root-datum comparison and base-transport results. Semisimplicity and hence
connected reductivity come from the supplied `TitsIndexData`. The theorem
does not prove that the original group becomes split, construct a maximal
split torus, or construct an affine building. In the local anisotropic
application, `L` can be the actual maximal unramified subfield of the
separable closure; proving that its maximal split torus is a maximal torus
remains an independent obligation.
