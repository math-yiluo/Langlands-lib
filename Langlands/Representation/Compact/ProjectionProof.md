# Compact averaging is a natural projection

The theorem `Langlands.Compact.projectionAndNaturality` proves the entire
accepted proposition `ProjectionAndNaturality` over its three independent
universes. It uses the original topological-group, smoothness, compact open
subgroup, and complex-module hypotheses, with no topology on either module.

For a finite orbit, each group element permutes the orbit. The proof of
`orbitMean_invariant` moves the linear action through the scalar and finite sum,
then uses `Equiv.sum_comp` for this permutation. Thus the normalized orbit mean
is invariant.

If the starting vector is fixed, every orbit vector equals it.
`orbitMean_id` rewrites the sum as the orbit cardinality times this vector.
The orbit is nonempty, so its finite cardinality is nonzero in the complex
numbers. Multiplication by its inverse cancels the normalization.

For a smooth representation restricted to a compact open subgroup, the accepted
`finite_orbit_of_smooth` supplies the required finite-orbit instances.
`averageMap_mem_fixedVectors` and `averageMap_id` apply the two preceding
algebraic lemmas. Together they give `averageMap_isProj`, using the two clauses
of `LinearMap.IsProj`: landing in the fixed-vector submodule and acting as the
identity there.

For naturality, `averageMap_commute` applies the accepted `orbitMean_map` to the
restricted representations and the given intertwiner. That lemma uses equal
fibers between finite transitive orbits to compare their normalized sums.
Extensionality turns the pointwise identity into the required equality of
complex linear maps. The closing theorem combines this identity with the
projection property.

The module retains all four component lemmas above for the subsequent
fixed-vector surjectivity argument. It uses finite sums, with no integration.
Worker 5 authored the proof and original explanation. Worker 23 checked the
implementation against the bound target and prepared this submission; the Lean
proof bytes are unchanged from Worker 5's shared draft.

The exact accepted target is statement artifact
`91124244-2c99-4f10-91d2-bcab3a34712c`, version 1, effective snapshot
`32a1eb794b227e9454b3987494c3dc1b5ab37272892d647e1173506901404411`,
published at commit `ca9ae8528fa0040956297fdf3c11fd9a8f1df4f5`.
Its proposition fingerprint is
`ee00f4e7fe0fbb115b3874488ac89749fcc95fe5c50bedec3918b29886685bbd`.
The proof task is `849a1dbe-68d3-4bc8-9c67-ca059539e827`, revision 1.

The exact definition dependencies are:

- Compact averaging artifact `ed385ab4-3443-4345-a7c7-5d91c74940f9`, version 1,
  including `FiniteMean`, effective snapshot
  `aad5d14b4a17fc183be073cb292549ca0522d206c40cf3977960e1ddf23caebc`,
  publication commit `93def8b48b4703317be20fe31714dddf482835a9`.
- Smoothness and fixed-vector artifact `665022df-625b-44ae-9dbd-425f6e266bab`,
  version 1, effective snapshot
  `092f2dc612370a1612d3c08d1e60ff18add554e831ee02c7041342ac9dff16c0`,
  publication commit `10c81beaaff024987cf2945c64d0c9511f6cb686`.

The source of the target is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II: *Smooth representations*,
June 16, 2019, Section 1, pages 3-4: normalized projection and the finite-coset
formula in Proposition II.1.2. Naturality is an internal algebraic consequence
of that formula. Literature ID `casselman-2019-smooth-representations`,
content SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Retained original:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation is development validation. Independent proof checking, semantic
review, and publication supply acceptance separately.
