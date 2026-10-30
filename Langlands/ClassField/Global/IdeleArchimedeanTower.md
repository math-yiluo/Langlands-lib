# Archimedean idele invariants under inflation

This internal supporting module proves that inflation of actual idele cohomology
preserves each archimedean invariant and the sum of these invariants at compatible
choices of places. For the inflation theorems, `F ⊆ E ⊆ L` is a scalar tower of
number fields, with both `E/F` and `L/F` Galois. All three fields lie in an arbitrary
common universe. For every infinite place `q` of `L` and every class
`x ∈ H²(Gal(E/F), J_E)`, the invariant at `q` of the inflation of `x` equals the
invariant of `x` at the pullback of `q` to `E`.

`archimedeanIdeleInvariantSum` is the additive map obtained by summing the existing
archimedean idele invariants over all infinite places of `F`, with one explicit
chosen place of `E` above each. This definition only needs an extension `E/F` of
number fields, with no Galois hypothesis. Its inflation identity uses the Galois
scalar tower above and explicit upper and lower choices: each upper chosen place
must pull back to the corresponding lower chosen place. No hypotheses on a
finite-place local invariant family enter these archimedean results.

The coordinate lemmas first show that an embedding of fields into one another
preserves the real part of the complex value of a completed element at a place
and its pullback. These lemmas require fields only. The proof uses density of the
field in its completion and continuity of the real part; the canonical complex
embeddings on the dense field agree up to complex conjugation, which preserves
real parts. The sign class consequently agrees. Specializing to number fields
and their actual idele inclusion gives preservation of the sign class of an
infinite idele coordinate, without any Galois assumption.

The cocycle evaluation lemmas apply to an arbitrary base field `F` and a number
field `E` with an `F`-algebra structure. Uniqueness of complex conjugation allows
evaluation at any nonidentity stabilizer element. A trivial stabilizer gives
zero. For a scalar tower with `E` and `L` number fields and `E/F` normal, the
conjugation value of an inflated cocycle is the included lower conjugation value,
by the actual coefficient map and normal restriction of automorphisms.

For the main theorem, represent a degree-two class by a cocycle. If the upper
place has nontrivial stabilizer, restrict its conjugation to `E`. When the
restriction is nontrivial, the two cocycle formulas and the coordinate sign
identity give the result. When it is the identity, the lower place is real and
has trivial stabilizer. The upper value is then the square of an included idele
coordinate fixed by conjugation, hence has zero sign class. If the upper
stabilizer is trivial, unramifiedness descends to the lower place and both
invariants vanish. Summing the pointwise identity proves the sum identity.

The provenance is internal: the module derives these results from
`IdeleArchimedean`, `IdeleCohomologyTower`, `ReciprocityTower`, the actual arithmetic
completion maps, and Mathlib's completion and infinite-place APIs. The proof
adapts the stabilizer case split of `ReciprocityTower` to idele coefficients;
the additional completion argument is needed for arbitrary idele coordinates.
This pair does not assert a total finite-plus-infinite formula, restriction
scaling, or the existence of the global invariant family on idele-class
cohomology. That existence is the separate statement `GlobalInvariantStatement`,
which keeps a local invariant family satisfying the class-formation and
arithmetic-normalization laws as a hypothesis. It is proved as
`globalInvariantStatement` in `Langlands.ClassField.Global.InvariantProof`.
