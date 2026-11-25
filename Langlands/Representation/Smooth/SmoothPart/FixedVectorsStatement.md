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

The direct project imports are:

- `SmoothPart.FixedVectorsDefinitions`.
- `Smooth.FixedVectors.Definitions`.

Their transitive project definitions are the smooth-part construction
`Langlands.Representation.Smooth.SmoothPart.Definitions` and the foundational
smoothness definitions `Langlands.Representation.Smooth.Definitions`.
The complete eight-file source closure was verified at preparation. No
project proof is a dependency.

For an open `K`, every original `K`-fixed vector is smooth with witness `K`.
The equivalence therefore preserves the underlying vector in both
directions. Both composites in the naturality square have underlying function
`v ↦ f v`, justifying these three internally derived laws under the stated
generality. This is a definition returning `Prop`; it assumes none of these laws
as a theorem. `FixedVectorsProof.lean` proves the entire target as
`Langlands.smoothPartFixedVectors`, introducing the topological-group instance
at the proposition's internal binder.
The preparation environment pins Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
