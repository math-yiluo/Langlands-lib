# Compact averaging is a natural projection

The theorem `Langlands.Compact.projectionAndNaturality` proves the entire
proposition `ProjectionAndNaturality` over its three independent
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

For a smooth representation restricted to a compact open subgroup, the published
`finite_orbit_of_smooth` supplies the required finite-orbit instances.
`averageMap_mem_fixedVectors` and `averageMap_id` apply the two preceding
algebraic lemmas. Together they give `averageMap_isProj`, using the two clauses
of `LinearMap.IsProj`: landing in the fixed-vector submodule and acting as the
identity there.

For naturality, `averageMap_commute` applies the published `orbitMean_map` to the
restricted representations and the given intertwiner. That lemma uses equal
fibers between finite transitive orbits to compare their normalized sums.
Extensionality turns the pointwise identity into the required equality of
complex linear maps. The closing theorem combines this identity with the
projection property.

The module retains all four component lemmas above for the subsequent
fixed-vector surjectivity argument. It uses finite sums, with no integration.
The implementation was checked against the exact target.

The exact target is `Langlands.Compact.ProjectionAndNaturality` (module
`Langlands.Representation.Compact.ProjectionStatement`), published at Library
commit `ca9ae8528fa0040956297fdf3c11fd9a8f1df4f5`.

The exact definition dependencies are:

- the compact averaging definitions `Langlands.Representation.Compact.Definitions`,
  including `FiniteMean`, published at Library commit
  `93def8b48b4703317be20fe31714dddf482835a9`.
- the smoothness and fixed-vector definitions
  `Langlands.Representation.Smooth.Definitions`, published at Library commit
  `10c81beaaff024987cf2945c64d0c9511f6cb686`.

The source of the target is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II: *Smooth representations*,
June 16, 2019, Section 1, pages 3-4: normalized projection and the finite-coset
formula in Proposition II.1.2. Naturality is an internal algebraic consequence
of that formula. Literature ID `casselman-2019-smooth-representations`,
content SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Retained original:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

Environment in which it was checked: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
