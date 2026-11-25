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

Direct dependencies are [the adjacent construction](FixedVectorsDefinitions.md)
and `Smooth.FixedVectors.Definitions`. The former is published at
`9db46907db3181b0c1dfd287b8ab2f1f02054cab`; the latter is published at
`18d2c44b3fecb756a7634ce0f766fdc16b539b45`.
Both modules and their complete source closures were verified
at Library `196cb468ed4d64d896980a67063afd48f8285185`.

The transitive construction dependencies are
`Smooth.Contragredient.Definitions` (smooth contragredient),
`Smooth.SmoothPart.FixedVectorsDefinitions` (smooth-part fixed vectors),
`Dual.Definitions` (algebraic dual),
`Smooth.SmoothPart.Definitions` (smooth part) and
`Smooth.Definitions` (smoothness and fixed vectors), all under `Langlands.Representation`.
The statement imports no project proof. This is one proposition definition
with all four clauses; it is not an assumed theorem. It is proved by
`Langlands.smoothDualFixedVectors` in [FixedVectorsProof](FixedVectorsProof.md).

These are internal naturality and evaluation identities for the restriction
in Casselman Proposition II.3.1, Chapter II, Section 3, page 6
(`casselman-2019-smooth-representations`,
SHA `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
June 16, 2019). They do not import that proposition's stronger isomorphism
assertion.
