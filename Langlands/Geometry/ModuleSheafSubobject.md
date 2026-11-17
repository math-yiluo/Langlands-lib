# Module sheaf subobjects detected by actual stalk images

This internal helper detects inclusion and equality of categorical subobjects
of an actual module sheaf using its actual stalk colimits. Its provenance is
the sheaf section-extensionality theorem and the universal property of
cokernels in an abelian category. No original-literature theorem is asserted.

The parameters are any commutative ring R and any topological space X, with
R, X and all module values in one universe. The sheaves take values in
`ModuleCat R`; their coefficients are fixed across X.

`hom_ext_stalk` proves that two sheaf maps agree if their actual stalk maps
agree at every point. It applies section extensionality to each component,
then the formula expressing a stalk map on a germ.

`stalkImage f x` is the linear range of the actual stalk map induced by f.
For two monomorphisms f and g into a common sheaf,
`subobject_mk_le_iff_stalkImage_le` proves that the subobject represented by
f is contained in the subobject represented by g exactly when their stalk
images have that inclusion at every point.

In the forward direction, the factorization of f through g induces a
factorization on each stalk. In the reverse direction, compose f with the
cokernel projection of g. Every stalk element in the image of f is in the
image of g, so this composite vanishes on every stalk. `hom_ext_stalk`
therefore proves that the composite sheaf map is zero. The abelian
`monoLift` construction factors f through g, proving the subobject
inclusion.

`subobject_mk_eq_iff_stalkImage_eq` applies the inclusion result in both
directions. The conclusion is actual equality in `Subobject N`, rather
than merely an isomorphism of the two source sheaves. No local freeness,
finite generation, topological separation or nonemptiness assumption
is required. Pullback comparisons and particular exterior subsheaves
are subsequent consumers.
