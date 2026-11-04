# Vector coordinates for split commutative extensions

Worker 1485. This internal derived unit constructs natural coordinates for a
split commutative extension from its actual full kernel and a group-scheme
section. It uses only the existing group-object laws and all-test kernel and
vector-group definitions, with no external classification input.

Let `j : K ⟶ E` be monic on underlying relative schemes, let `q : E ⟶ V`,
and suppose the range of `j` is the full kernel functor of `q`. Assume `E`
is commutative and `s : V ⟶ E` is a group section of `q`. On every test
scheme, multiplying an included kernel point and a section point defines a
multiplicative equivalence `K(T) × V(T) ≃ E(T)`. Injectivity follows by first
applying `q`, cancelling the section factor, then using that `j` is monic.
Surjectivity writes `x` as its kernel factor `x s(q(x))⁻¹` times `s(q(x))`.
Both the equivalence and its inverse commute with every test morphism.

Given natural `n`-dimensional vector coordinates on `K` and one-dimensional
vector coordinates on `V`, `isVectorGroupOfDimension_of_section` joins them
with the quotient coordinate first to obtain natural coordinates of dimension
`n + 1` on `E`. The kernel may have dimension zero. No geometric hypothesis
or field hypothesis is needed for this coordinate construction.
