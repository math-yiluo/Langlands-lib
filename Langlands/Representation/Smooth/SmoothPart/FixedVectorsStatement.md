# Fixed vectors of smooth parts: target

`Langlands.SmoothPartFixedVectorsStatement` has three clauses. The forward
equivalence and its inverse preserve the underlying vector, and the equivalence
commutes with every intertwiner restricted to smooth parts and then to
`K`-fixed vectors. In the naturality equation, `K` is the same open subgroup
on both sides, while the two representation spaces have independent universes.
The topological-group hypothesis is quantified explicitly within the proposition.

The coefficients are an arbitrary commutative ring; the representations need
not be smooth. The statement needs no compactness, finiteness, or averaging.
It is internal functorial infrastructure derived from the construction in
[FixedVectorsDefinitions](FixedVectorsDefinitions.md) and the fixed-vector
map construction. The source conventions are Casselman Chapter II, Section 1,
page 2, first two paragraphs (`casselman-2019-smooth-representations`,
SHA `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
June 16, 2019); the naturality equation is a project formulation.

The direct project imports are independently published constructions:

- `SmoothPart.FixedVectorsDefinitions`, artifact
  `8bf36df6-8b13-4713-89e0-7d2ba5aa6824` version 1, published at
  `a158df54c354b831c3b158cd0a299f3f78acb9da`, with receipt
  `51c5f743-c16d-4e28-919b-c64311bd5224`.
- `Smooth.FixedVectors.Definitions`, artifact
  `7ad85b8b-caae-4345-ac1b-2c2d551dbb94` version 1, published at
  `18d2c44b3fecb756a7634ce0f766fdc16b539b45`, with receipt
  `7f5084d1-9e75-445b-b031-b754e38c4830`.

Their transitive project definitions are the smooth-part construction
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` version 1 and foundational
smoothness definitions `665022df-625b-44ae-9dbd-425f6e266bab` version 1.
Current publication and the complete eight-file source closure were verified at
`bb596ce619f2174816281f508cce65b3303beeb4`; the normal and draft copies match
all effective published hashes. No project proof is a dependency.

For an open `K`, every original `K`-fixed vector is smooth with witness `K`.
The accepted equivalence therefore preserves the underlying vector in both
directions. Both composites in the naturality square have underlying function
`v ↦ f v`, justifying these three internally derived laws under the stated
generality. This is a definition returning `Prop`, proposed as one coherent
target for independent review; it assumes none of these laws as a theorem.
The prepared environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
pinning Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
