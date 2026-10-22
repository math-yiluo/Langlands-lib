# Compact-open fixed-vector duality

For a smooth complex representation `rho` of a topological group and a specified
compact open subgroup `K`, restriction from the `K`-fixed smooth dual to the
algebraic dual of the original `K`-fixed space is bijective. The restriction is
the existing linear map `smoothDualFixedRestriction`; bijectivity therefore
asserts an isomorphism of complex vector spaces without choosing a new map.

The group and module have independent universes. The topological-group instance
is quantified inside the proposition. Smoothness, openness and compactness are
explicit hypotheses. There is no topology on the module, no finite dimension,
admissibility, countability, Hausdorffness or global local compactness hypothesis.

## Source and scope

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II, June 16, 2019, Section 3, Proposition II.3.1, page 6, states this
restriction isomorphism. Section 1, Proposition II.1.2, pages 3-4, gives its
averaging decomposition proof. Page 1 specifies the chapter's stronger ambient
locally profinite and countability hypotheses and Noetherian rational
coefficient rings.

This version specializes the coefficients to complex numbers, matching the
accepted averaging construction, and needs only a specified compact open
subgroup. Smoothness makes each orbit under that subgroup finite; a normalized
finite sum therefore gives the needed inverse. The original source was read,
including its ambient conventions.

Literature ID: `casselman-2019-smooth-representations`.
SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Actual file:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Development dependencies

The statement imports accepted fixed-functional construction
`9a629b79-9346-46b2-950a-7c31ed1b5587`, version 1, published at
`9db46907db3181b0c1dfd287b8ab2f1f02054cab`, with independent receipt
`b2938ccc8de248d8b66eaca960639ca3`. Its five transitive construction
dependencies are accepted version 1 of
`be3f8221-aa6f-4069-8faa-f04e1f5dc4b7` (smooth contragredient),
`8bf36df6-8b13-4713-89e0-7d2ba5aa6824` (smooth-part fixed vectors),
`079d7c1a-8b96-4917-997a-536d6954d55b` (algebraic dual),
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` (smooth part), and
`665022df-625b-44ae-9dbd-425f6e266bab` (smoothness and fixed vectors).
Their complete twelve-file effective source closure was verified current at
Library `196cb468ed4d64d896980a67063afd48f8285185` and matches the local
sources. No project proof is imported by the statement.
This proposition definition is proposed for independent statement review;
the adjacent complete proof and its finite-mean helpers remain one draft.

The adjacent proof uses the accepted compact-averaging construction
`ed385ab4-3443-4345-a7c7-5d91c74940f9`, version 1. It does not assume the
separately pending projection or fixed-vector-surjectivity proofs.
Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
