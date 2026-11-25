# Surjectivity on compact-open fixed vectors

`Langlands.Compact.FixedVectorSurjectivity` states that a surjective complex
linear intertwiner between two smooth representations of a topological group
induces a surjection between their submodules fixed by a compact open subgroup.
Both smoothness assumptions, the subgroup's openness and compactness, the
intertwiner condition, and its surjectivity are explicit. The vector spaces
carry no topology.

Original source: Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter II: *Smooth representations*, revision June 16, 2019,
Section 1, Proposition II.1.3, page 4: the right-surjectivity clause of the
sequence on fixed vectors. The normalized projection and finite-coset formula
on pages 3-4 supply the averaging method.

Source ID: `casselman-2019-smooth-representations`. Content SHA256:
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Actual file:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

This is the surjectivity clause, not a claim of the full categorical exactness
theorem. Preservation of smoothness by subrepresentations and quotients is a
separate result, not stated here. The present coefficients are exactly `Complex`;
the proof requires the invertibility of nonzero finite cardinalities and does
not justify a statement over arbitrary coefficient rings. Local profiniteness
and countability from the chapter's ambient setup are unnecessary here.

This file only defines a proposition, with no proof placeholder; the proof is
`fixedVectorSurjectivity` in `SurjectivityProof`.
Its project dependencies are the compact averaging definitions
(`Compact.Definitions`) and the published smoothness definitions
(`Smooth.Definitions`). The compact definitions were
published at Library commit `93def8b48b4703317be20fe31714dddf482835a9`.
Environment in which it was checked:
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
