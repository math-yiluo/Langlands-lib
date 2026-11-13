# Tensor decomposition for finite unramified integer rings

Let `F` be a nonarchimedean local field with its given valuation and topology.
Let `E` be an actual finite Galois intermediate field in its separable closure,
and suppose `ArithmeticUnramified F E`. The rings in this construction are
`baseIntegers F` and `extensionIntegers F E`, formed from the established local
norm on `F` and its spectral extension to `E`.

The actual map from field automorphisms to residue-field automorphisms is
bijective. Its surjectivity is the published `residueHom_surjective`.
Both residue fields are finite. Their Galois automorphism count is their
extension degree; unramifiedness identifies that degree with `[E:F]`, which is
also the number of field automorphisms. Thus surjectivity and the equal finite
cardinalities give bijectivity.

Distinct field automorphisms therefore differ on some residue class. Lift
that class to an integer. The difference of the integer images has nonzero
residue and is a unit. The derived `AutomorphismTensor` equivalence now applies:
the integer ring of `E` is finite free over that of `F`, with rank `[E:F]`.
The resulting actual algebra equivalence sends `a ⊗ b` to
`σ ↦ a * integerAut F E σ b`.

This is an internal application of the published local arithmetic and residue
action results and the derived tensor decomposition. It constructs no group
scheme action or descent datum.
