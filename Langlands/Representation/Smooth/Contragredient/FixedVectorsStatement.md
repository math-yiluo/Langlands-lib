# Fixed smooth functionals: target

`Langlands.SmoothDualFixedVectorsStatement` records four properties:

1. The open-subgroup equivalence preserves evaluation on every vector.
2. Restriction to the fixed submodule evaluates a functional on the same vector.
3. For an open subgroup, restriction factors through the full-dual fixed
   functionals by `smoothDualFixedEquiv`.
4. For any subgroup, restriction commutes with contravariant pullback along
   every intertwiner, using the linear dual of the induced fixed-vector map.

The two representation spaces have independent universes. The coefficient
ring is commutative; a compatible topological-group instance is explicitly
quantified inside the proposition. Original smoothness, admissibility,
compactness, and characteristic zero are not hypotheses of these four
elementary identities. The restriction map is not asserted to be bijective.

Direct dependencies are [the adjacent construction](FixedVectorsDefinitions.md),
accepted artifact `9a629b79-9346-46b2-950a-7c31ed1b5587` version 1,
and `Smooth.FixedVectors.Definitions`, accepted artifact
`7ad85b8b-caae-4345-ac1b-2c2d551dbb94` version 1. The former is published at
`9db46907db3181b0c1dfd287b8ab2f1f02054cab`, with independent receipt
`b2938ccc8de248d8b66eaca960639ca3`; the latter is published at
`18d2c44b3fecb756a7634ce0f766fdc16b539b45`.
Both exact versions and their complete effective source closures were verified
current at Library `196cb468ed4d64d896980a67063afd48f8285185`.

The transitive construction dependencies, all at accepted version 1, are
`be3f8221-aa6f-4069-8faa-f04e1f5dc4b7` (smooth contragredient),
`8bf36df6-8b13-4713-89e0-7d2ba5aa6824` (smooth-part fixed vectors),
`079d7c1a-8b96-4917-997a-536d6954d55b` (algebraic dual),
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` (smooth part) and
`665022df-625b-44ae-9dbd-425f6e266bab` (smoothness and fixed vectors).
The statement imports no project proof. This is one proposition definition
proposed for independent review, with all four clauses and their adjacent
proof helpers kept together; it is not an assumed theorem.

These are internal naturality and evaluation identities for the restriction
in Casselman Proposition II.3.1, Chapter II, Section 3, page 6
(`casselman-2019-smooth-representations`,
SHA `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
June 16, 2019). They do not import that proposition's stronger isomorphism
assertion. Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1.
