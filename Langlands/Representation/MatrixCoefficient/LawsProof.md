# Proof of the matrix-coefficient laws

`Langlands.matrixCoefficientLaws` proves the complete accepted proposition
`Langlands.MatrixCoefficientLawsStatement`. Worker 0 authored the proof and its
component lemmas. Worker 55 checked the source conventions and effective
dependencies, retained the proof terms unchanged, and prepared this documentation
and submission. All helpers remain in this single proof module.

The four independent universes are `uR`, `uG`, `uV`, and `uW`, for the coefficient
ring, group, source module, and target module. The closing theorem assumes only
`CommRing R`, `Group G`, and the two additive commutative groups and module
structures. The topology and topological-group assumptions are quantified
inside the clauses that need them. There is no topology on the coefficients or
modules, and no admissibility, compactness, finite-generation, or
finite-dimensionality assumption.

## Implemented proof

`matrixCoefficient_apply` unfolds the bilinear construction. Right translation
is the representation's multiplication law, evaluated by the functional.
Left translation uses the same law and the inverse in Mathlib's dual action;
the inverse of the inverse cancels. Naturality follows pointwise from the
intertwining equation, using `dualIntertwining` as pullback of functionals.

For two smooth factors choose open fixing subgroups `K` and `L`. Their
intersection fixes the coefficient on both sides. For left multiplication
by `k`, use the fixing equation for the dual at `k⁻¹`; membership follows
from closure of `K` under inverses. For right multiplication by `l`, use
the fixing equation for the vector. The translation identities finish the
proof. This part uses no continuity of group operations.

For local constancy, fix a smooth vector and choose its open fixing subgroup
`K`. At a group element `g`, the open set
`{h | g⁻¹ h ∈ K}` contains `g`. Continuity of multiplication in the topological
group gives openness. On this set write `h = g (g⁻¹ h)` and use the fixing
equation, so the coefficient equals its value at `g`. The Mathlib
`IsLocallyConstant.iff_exists_open` criterion gives the conclusion.
This requires no smoothness assumption on the functional.

The closing proof assembles the two translation equalities and the three
remaining helper theorems into the four-clause conjunction. It does not import
any project proof module.

## Source and scope

The implemented route is an internal derivation using the normalization and
uniform-smoothness assertion in Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, revision June 16, 2019,
Section 7, page 10, first paragraph. Section 3, page 6, defines the inverse
dual action; Section 1, page 2, defines smooth vectors using open fixing
subgroups. The original's ambient assumptions on page 1 include local
profiniteness, countability conditions, and a Noetherian coefficient ring
containing the rationals; Section 7 starts with an admissible representation.
The direct arguments above justify the accepted target's weaker assumptions.
They assert neither Casselman Proposition II.7.1 nor a support characterization
or the local Langlands correspondence.

- Literature ID: `casselman-2019-smooth-representations`.
- Original SHA256:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Actual original file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

Worker 55 reread pages 1, 2, 6, and 10 and verified the original file's SHA256.
In particular, the matrix coefficient uses `rho(g)` with no inverse, whereas
the algebraic dual uses `rho(g⁻¹)`. The left-translation formula applies that
dual action at `h⁻¹`, exactly as in the accepted target.

## Exact target and dependencies

The accepted target is `e850d833-de95-42c7-acbd-29cdfcad52e7` version 1,
`Langlands.MatrixCoefficientLawsStatement`, with fingerprint
`3f33cc1ead724e4faa787ecb1ec2aa921c87eb2de5c930fb59661b576d951321`. It was published at
`9db46907db3181b0c1dfd287b8ab2f1f02054cab` and is current at
`5bc58c2525e0499012801c80f17b6a9c04d57263` when checked for this submission.
Its independent semantic receipt is
`b7fbd641b5db422e8a9099aa94149fea`. All 8 effective
target and dependency source files match the workspace byte for byte.
The proof imports only that target. Its exact project definition dependencies,
all accepted, published, and current at the checked Library commit, are:

- Matrix coefficients: `5352a743-a6a8-4824-b91e-1cbc32b79b30`, version 1.
- Algebraic dual maps: `079d7c1a-8b96-4917-997a-536d6954d55b`, version 1.
- Smoothness and fixed vectors: `665022df-625b-44ae-9dbd-425f6e266bab`, version 1.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The target imports `Mathlib.Topology.LocallyConstant.Basic`, which supplies
`IsLocallyConstant.iff_exists_open`.

The proof contribution is bound to task
`d472d77b-c3d3-42a4-9ff3-d8acbb94a2d7`, revision 1, module
`Langlands.Representation.MatrixCoefficient.LawsProof`, and declaration
`Langlands.matrixCoefficientLaws`. Required validation uses the shared
incremental Lake build and exact target inspection, including allowed
assumptions. Compilation is development evidence; independent semantic review
and current Library publication establish acceptance.
