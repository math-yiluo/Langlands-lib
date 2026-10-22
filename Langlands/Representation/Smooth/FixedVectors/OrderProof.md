# Fixed-vector antitonicity

The closing theorem `Langlands.fixedVectorsAntitone` inhabits the complete
accepted proposition `Langlands.FixedVectorsAntitoneStatement`. The reusable
lemma `Langlands.fixedVectors_antitone` states the result for a specified
representation.

Both declarations retain the independent universes `uR`, `uG`, and `uV`.
Their hypotheses are exactly `[CommRing R] [Group G] [AddCommGroup V]
[Module R V]`. There are no topology, smoothness, finiteness, normality, or
additional coefficient hypotheses.

## Implemented proof

The lemma introduces subgroups `H` and `K`, containment `hHK : H ≤ K`,
a vector `v`, and its membership `hv` in `fixedVectors ρ K`.
Submodule containment is reduced to this elementwise implication.

The accepted fixed-vector definition is the invariant submodule of the
representation restricted to a subgroup. Unfolding that meaning by `change`
makes the goal `∀ h : H, ρ (h : G) v = v`.
For each `h : H`, the proof `hHK h.property` shows that its underlying group
element belongs to `K`. The subtype element `⟨h, hHK h.property⟩ : K` can
therefore be supplied to `hv`. The resulting equation is exactly the required
fixing equation for `h`, since the underlying group elements coincide.

The closing theorem is the lemma itself, at the full universally quantified
accepted proposition. No specialization of a universe or hypothesis is hidden
in the closing step. The file imports only the accepted statement module.

## Provenance and exact dependencies

Worker 0 authored the proof in the public draft for this task, revision 1,
content key
`f260c7afc2b5196c582a752d503022a5d998314659d0f59aa3a797c1c736c67f`.
Worker 13 reused that Lean proof unchanged, checked its exact dependencies,
and expanded this documentation. Both workers are submission coauthors.
The draft is provenance for the authored code, not an accepted theorem
dependency.

The exact target is statement artifact
`81e1f095-d4a9-4b4c-ae57-d746ec2fb206`, version 1:

- Module: `Langlands.Representation.Smooth.FixedVectors.OrderStatement`.
- Declaration: `Langlands.FixedVectorsAntitoneStatement`.
- Proposition fingerprint:
  `dca27403b4ffd81996e8387f89562eec96e937264c281cfd1d1f3215ca62af43`.
- Published commit: `7a6371a96dfb5d98ab67306ec55b35646ca9d94e`.
- Independent review receipt: `93362fb9-0f77-4c43-b82a-d4532b844a18`.
- Lean SHA256:
  `389c9e2199166192fe43d4be65b8b1bc026fea2378a663c2118301320ab76f07`.
- Markdown SHA256:
  `e4615f07daf678bf601a95996369f5d4d602f88f3a768a0c63345b012d58eb63`.

The sole project definition dependency is artifact
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1,
`Langlands.Representation.Smooth.Definitions`, published at
`10c81beaaff024987cf2945c64d0c9511f6cb686`, with independent receipt
`a26076cd-7da3-4621-992f-5c0207f7fe1e`. Its Lean and Markdown SHA256 values are
respectively
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` and
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
The fetched records confirm both dependencies are accepted, published,
and current; their effective source pairs match the local imports.

The original fixed-vector meaning comes from Bill Casselman,
*Introduction to admissible representations of p-adic groups*, Chapter II,
revision June 16, 2019, Section 1, page 2, first paragraph:
`literature_id` `casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The retained original PDF is
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
The antitonicity argument is an internal elementary derivation from this
meaning, not a separately numbered theorem attributed to Casselman.

## Validation boundary

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.

The file contains a complete Lean proof with no placeholders or introduced
axioms. Development compilation is not independent proof acceptance.
The proof task pins the exact target, environment, module, and closing theorem;
submission must pass the registered independent checker, independent semantic
review, and publication to the current Library.
