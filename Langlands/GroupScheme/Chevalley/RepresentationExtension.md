# Ambient subquotients for actual corepresented closed subgroups

This internal derived construction combines `CoefficientEmbedding`,
`RegularQuotient`, stable inverse images, and coordinate reindexing. Its main
implemented conclusion is `exists_corepresented_ambient_subquotient`. For actual
corepresented group functors `H → F` over an arbitrary field `k : Type u`, if the
actual group-scheme map is a closed subgroup inclusion, every actual
finite-dimensional representation of `H` is a subquotient of a restricted actual
finite-dimensional representation of `F`.

Here `IsSubquotientOf` has its existing meaning: an intermediate actual
representation has an injective intertwiner into the ambient representation and
a surjective intertwiner onto the desired representation. Every intertwiner is
required to commute with the actual matrices on every affine algebra test,
including nonreduced tests.

`copyMatrix C` is the Kronecker product of a coordinate matrix `C` and the
identity matrix on a finite copy index. Its multiplication formula applies `C`
independently to each copy, and surjectivity follows by choosing preimages one
copy at a time. It intertwines the tensor products with the corresponding trivial
representations whenever `C` intertwines the original actual representations.
The proof uses the actual tensor coefficient formula on all affine tests.
Trivial representations commute with restriction, as follows from the unique map
to the terminal object.

The finite reindexing helpers identify the actual affine matrices after a change
of coordinate index with their entrywise reindexings. Matrix multiplication is
preserved because the intermediate coordinate map is an equivalence. The
associated coordinate linear equivalences preserve injectivity and surjectivity.
Reindexing the actual representation also commutes with restriction.

For the main construction, surjective coordinate restriction lifts every
universal matrix coefficient of the subgroup representation into the ambient
coordinate algebra. Let `V` be the finite regular span of these lifts and `W` its
image in the subgroup coordinate algebra. The image is regular, finite, and
contains all original coefficients. The coefficient embedding injects the
subgroup representation into finitely many copies of the regular representation
on `W`. The regular quotient map from `V` to `W` gives an actual equivariant
surjection from the same number of copies of the restricted ambient regular
representation. After reindexing the copy coordinates by `Fin` of their
cardinalities, `isSubquotientOf_of_common_quotient` takes the inverse image of the
injected representation. This is the required actual subquotient witness.

The construction does not require finite type, smoothness, connectedness,
infinitude, perfection, a splitting field, or a positive dimension. Finite empty
coordinate sets are allowed. Its scope here is the explicitly corepresented
models. Transport to arbitrary affine group schemes, semisimplicity reflection,
and the host Cartan-generation proof remain separate steps.
