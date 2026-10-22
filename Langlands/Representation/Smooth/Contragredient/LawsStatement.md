# Smooth contragredient laws: proposition target

`Langlands.SmoothContragredientLawsStatement` defines one coherent proposition
target. Over a commutative ring, a group with a topology, and three
independently universed modules, it explicitly quantifies a topological-group
instance and asserts eight clauses:

1. Every smooth contragredient is smooth, even if the original action is not.
2. The action on a functional is precomposition with the inverse group element.
3. Evaluation is invariant under acting on both the functional and the vector.
4. The contragredient map is pullback of functionals.
5. It preserves the identity intertwiner.
6. It reverses composition of intertwiners.
7. For a smooth original action, the canonical smooth bidual map is evaluation.
8. That bidual map is natural between two smooth representations.

The last clause explicitly assumes smoothness of both source and target.
No admissibility, reflexivity, freeness, finite dimension, or compactness is
claimed or assumed. No topology is placed on the coefficient ring or modules.
The statement imports only the accepted contragredient construction pair,
with its dependency chain documented in [Definitions](Definitions.md).

These are internal consequences of the smooth-part and algebraic dual
constructions. Every smooth functional has an open fixing subgroup, which
also fixes the corresponding vector in the restricted action. The remaining
clauses compare the underlying functional evaluations and composite maps.
These direct arguments justify the stated generality beyond the source's
ambient hypotheses. The invariant pairing is expressly described in Casselman:
`casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, revision June 16, 2019, Section 3, page 6, opening paragraphs.
The contravariant morphisms are described after Corollary II.3.3 on the same
page. The construction and naturality of the bidual evaluation map are
internally derived; Lemma II.3.2's isomorphism claim is not part of this target.
The original file is
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Exact dependencies

The sole direct project import is
`Langlands.Representation.Smooth.Contragredient.Definitions`, accepted artifact
`be3f8221-aa6f-4069-8faa-f04e1f5dc4b7`, version 1, published at
`933f2719b54fcf01bebb367c9cae56b8d5f17edc`, with independent receipt
`60084e7c-d793-42be-9a0a-6906ca4a95e9`.
Its effective Lean SHA256 is
`878b6130d7c563ead853cbdd50a6c70aac01f9104062049e696f9e68cbb30de3`;
its effective Markdown SHA256 is
`531fc58fb846d22f48363964f7fb5af0ab9459747c7ca08a683df6ada7c8aae0`.
The full project definition closure consists of the following version-1
artifacts, all accepted and currently published:

- Algebraic dual constructions `079d7c1a-8b96-4917-997a-536d6954d55b`.
- Smooth-part constructions `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`.
- Smoothness definitions `665022df-625b-44ae-9dbd-425f6e266bab`.

No adjacent property or proof module is imported. The environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.
Worker 0 authored this target. Independent statement review and subsequent
proof acceptance are separate obligations.
