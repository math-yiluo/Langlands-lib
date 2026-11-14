# Counting cocharacter weights in a homogeneous extended basis

This derived helper works over an arbitrary field `K`, a finite-dimensional
left division `K`-algebra `D`, a first-kind involution `sigma`, a quadratic form
`q` on a finite row module `n -> D`, and an actual cocharacter `f` of its
isometry group. The integer weight spaces are the existing all-test
`cocharacterWeightSpace`; their coefficient extensions are the actual
`cocharacterWeightSpaceOver` from the scalar-extension module.

For any field extension `L/K`, suppose `b` is an `L`-basis of
`L tensor_K (n -> D)`, with finite index `I`, and each basis vector `b i`
belongs to the extended weight space of the integer `w i`.
`cocharacterWeightBasisOver` restricts this basis to the indices with
`w i = c`, producing a basis of the actual extended weight-`c` space.
The resulting dimension is the number of such indices. Combining this with
the scalar-extension dimension theorem gives

`Nat.card {i : I // w i = c} = finrank K D * finrank D (cocharacterWeightSpace q f c)`.

The proof first tensors the published Laurent coefficient projector to `L`.
The canonical weight-space base-change equivalence lets it test any extended
weight vector by induction on a tensor of an original weight vector. The
original coefficient-isolation law then shows that the extended projector
fixes weight `c` and kills every other integer weight. Expand a vector of
weight `c` in the supplied basis and apply this projector. The terms of other
weights vanish, so precisely the matching basis vectors span the weight
space. Their independence is inherited from the supplied basis, giving the
restricted basis and its dimension formula.

This is an internal derivation from the published coefficient projectors,
actual scalar-extension equivalence, and ordinary basis and dimension
properties. It asserts no additional literature result. The finite index may
be empty, and there is no infinitude, characteristic, perfectness, separability,
centrality or nondegeneracy hypothesis. All base fields, coefficient extensions
and division algebras remain in the original universe `u`; the finite basis
index may be in any universe.

The helper assumes a homogeneous basis of the extended representation. It
does not construct a Morita comparison or that basis, identify the type-D
characters, or descend those characters. Those remain obligations of
`SpinCoverVectorWeightsStatement`.
