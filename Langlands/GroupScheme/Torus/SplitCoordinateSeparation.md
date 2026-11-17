# Separation of split-torus coordinates

This is an internal auxiliary result for descent of permutation atlases. Its
provenance is the published split-torus point model, the residue field map of a
scheme point, and the elementary dual-number construction in Mathlib. It makes
no independent literature claim.

For any nonempty scheme `S`, `exists_test_unit_ne_one` constructs a relative
affine test with a global unit unequal to one. Choose a point `s`, let `k` be its
residue field and use `Spec (k[ε]) → Spec k → S`. The dual number `1 + ε` is a
unit with inverse `1 - ε`; its second component shows that it differs from one,
including in characteristic two. The global-section isomorphism for a spectrum
transports this unit to the test scheme.

`index_eq_of_points_eq` states that two indices of a finite split torus over
a nonempty base are equal if their coordinates agree on every relative test
and every torus point. The proof uses the preceding test and the unit family
equal to `1 + ε` at one index and one at all other indices. The split-torus
point equivalence realizes this family by a torus point.
`indexMap_eq_of_points_eq` applies the result separately to every input index.

`reindex_eq_of_points_eq` needs no nonemptiness assumption. If two index maps
give identical reindexing of torus points on every relative test, they give
identical reindexing of functions with values in the global coefficient ring.
On a nonempty base the index maps themselves agree. On an empty base the ring
of global sections is a subsingleton, so both coefficient functions agree.
No constancy of permutations on disconnected bases is asserted.

`coefficientReindex S σ` is the actual algebra equivalence from functions on
`I` to functions on `J` over `Γ(S, ⊤)` that sends `z` to `z ∘ σ`, for an
equivalence `σ : J ≃ I`. Its inverse uses `σ.symm`.
`coefficientReindex_eq_of_points_eq` packages the preceding equality as equality
of these algebra equivalences.
