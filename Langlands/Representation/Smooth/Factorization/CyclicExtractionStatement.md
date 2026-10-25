# Cyclic local factors inside a two-factor representation

This pair states two derived prerequisites for constructing restricted-product
factorizations. It supplies no proof of either assertion. The group universes
`uG₁`, `uG₂` and carrier universe `uV` are independent throughout. Both groups
are Hausdorff locally compact totally disconnected topological groups, and the
global representation is an admissible irreducible complex representation of
their actual direct product.

`FirstFactorCyclicRefinementStatement` starts with any prescribed nonzero
vector `x`. It asks for a nonzero `y` in the first-factor orbit span of `x`
whose first-factor cyclic subrepresentation is admissible and irreducible.
Membership in the original orbit span is essential: every linear condition
preserved by the first action and satisfied by `x` remains satisfied by `y`.
The conclusion is not merely existence of some irreducible subrepresentation.

`SphericalFirstFactorCyclicStatement` assumes that the prescribed nonzero
vector `x` is fixed by a compact open subgroup `H` of the first factor and
that the actual spherical convolution algebra for `H` is commutative. It
states that the orbit span of this same `x` is already admissible and
irreducible as a representation of the first factor, and that its `H`-fixed
space has complex dimension one. The first group is equipped with its Borel
structure and a regular left Haar measure; no measure on the second group,
unimodularity, countability, or mass-one normalization is required.
`SphericalHeckeCommutative` is exactly the predicate from the published
restricted-product existence target, not a replacement by supplied abstract
algebra data.

In both assertions, an orbit span means `Langlands.Cyclic.orbitSpan` of the
restriction along `MonoidHom.inl`. Its carrier is a subspace of `V`, in the
same universe. The statements do not say that the whole first-factor
restriction is irreducible or admissible. The conjunction of these two
propositions is `TwoFactorCyclicExtractionStatement`.

## Derived provenance and intended use

These are internal consequences of the two-factor theorem and the
commutative-corner fixed-line argument, rather than verbatim numbered
statements from the literature. The original mathematical inputs are D.
Flath, *Decomposition of representations into tensor products*, Proceedings
of Symposia in Pure Mathematics 33, part 1 (1979), printed pp.179–183,
registered as `flath-1979-tensor-products`. The retained original is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
Printed p.179 (one-based PDF p.175) gives the fixed-space corner argument;
printed p.180 (PDF p.176) proves Theorem 1; and printed p.181 (PDF p.177)
states Example 2 and Theorem 2. The complete article was read in the parent
existence task. No applicable source errata was found in the supplied public
locations.

For the first statement, the published two-factor factorization and density
of the first-factor action on its irreducible factor can isolate a nonzero
simple tensor from the finite expansion of `x`. Its first-factor orbit span
is isomorphic to that factor. Alternatively the minimal fixed-space
argument in `TwoFactorExistenceProof` can be localized to the orbit span of
`x`. Either route must prove the asserted membership and admissibility.

For the second statement, write the global representation as the tensor of
its two irreducible admissible factors. A nonzero `H`-fixed vector forces the
first factor's `H`-fixed space to be nonzero. Commutativity of its actual
Hecke corner makes that fixed space a line. Tensor slices then show that
`x` is a simple tensor with nonzero first-factor component. Its orbit span
is isomorphic to the first factor. These explanations establish the
intended derivation and scope; they are not formal proof evidence.

In the restricted-product application, finitely many successive refinements
handle exceptional indices. At every other index, tail-fixedness and the
second statement give the required local irreducible cyclic factor without
changing the vector. Coherence of the resulting tensor maps and their
bijectivity remain separate obligations.
