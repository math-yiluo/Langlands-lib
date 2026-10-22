# Adelic extension norms

This construction uses the determinant norms of the actual completed
extensions in `Extension.lean`. At a base finite place, it takes their finite
product over all genuine primes lying above that place. This is a
multiplicative map; extension-of-scalars embeddings go in the opposite
direction and are different maps.

The index type is the subtype of Mathlib's height-one primes satisfying the
actual lies-over relation. Its finiteness is proved by injection into
Mathlib's finite set of primes above a nonzero prime. Restricted-product
well-definedness uses preservation of local integral subrings: exceptional
base places are contained in the image of the finitely many exceptional
extension places under restriction.

Continuity of the finite-adele norm is proved using the restricted-product
topology. On the stage where the coordinates in a cofinite set `S` are
integral, the image lies in the stage with exceptional set the image of
`S`'s finite complement under restriction of primes. Each coordinate is a
finite product of continuous local norms. The stagewise continuity criterion
therefore proves continuity for the full restricted product.

At an infinite place the construction takes the finite product over the
actual infinite places above it, using the completed-extension algebras from
Mathlib and `Extension.lean`. Finite products prove continuity. Combining
the infinite and finite factors gives `adeleNorm`; it is a monoid
homomorphism, since a field norm need not preserve addition.

`ideleNorm` maps the units of the actual adele ring by `Units.map`. Its
continuity uses the units topology, including both the element and its
inverse. `ideleNorm_val` records its underlying adele formula. The field
universes are independent throughout; no resizing is used.

The module also constructs the canonical comparison from `K_p` tensor `L`
over `K` to the product of the actual completions above `p`. The tensor and
diagonal formulas are proved at finite and infinite places, using the
actual completion embeddings and scalar towers.

At infinite places, `infiniteTensorEquiv` proves that this comparison is an
algebra equivalence. Restricting weak approximation for the infinite adele
ring to the places above `p` gives a dense image of `L`. This image lies in
the range of the comparison. That range is finite dimensional over the
complete nontrivially normed field `K_p`, so it is closed and the comparison
is surjective. Mathlib's sum of infinite inertia degrees identifies the
dimension of the product with `[L : K]`, also the dimension of the tensor
product. Surjectivity between these equal finite dimensions proves
bijectivity. The implementation proves the needed scalar tower through `L`
and supplies nontriviality of the completed norm using the element `2`.

Finite-place bijectivity, principal-norm compatibility and quotient descent
remain unproved. They are exposed as exact arithmetic obligations in the
paired `NormStatement` file; the statement is not used as an assumption in
this construction. No desired equivalence, norm or compatibility certificate
is assumed, and this group does not complete the task.

The defining product is Andre Weil, *Basic Number Theory*, second edition
(1973), Chapter IV section 1, Corollary 3, printed p. 64 (PDF p. 81).
The completed tensor-product comparison is Chapter III section 4,
Theorem 4, printed pp. 56-57 (PDF pp. 73-74); its norm corollary is printed
p. 58 (PDF p. 75).
The units topology and norm continuity are in Chapter IV section 3,
printed pp. 71-74 (PDF pp. 88-91); the distinction between embedding and norm
is explicit in Chapter VIII section 4, printed pp. 153-155 (PDF pp. 170-172).
Registered original: `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.

The arithmetic objects and the initial local norm maps are from
`Extension.lean`. Relevant pinned Mathlib support is
`NumberTheory/NumberField/{AdeleRing,InfiniteAdeleRing}`,
`NumberTheory/NumberField/Completion/Ramification`,
`RingTheory/DedekindDomain/Ideal/Lemmas`,
`Topology/Algebra/RestrictedProduct/TopologicalSpace`, the topological units
interface, and finite-dimensional linear algebra. Mathlib supplies the
infinite degree sum; this file does not claim an existing finite-place
completed tensor decomposition.
