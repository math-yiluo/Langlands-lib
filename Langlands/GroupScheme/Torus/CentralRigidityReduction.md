# From local central equality to local triviality

This internal reduction is derived from the published group-scheme definitions.
Its mathematical source is the deduction of SGA 3, Exposé IX, Corollary 5.2 from
Theorem 5.1, in the registered Gille–Polo 2009 recomposed edition
(`sga3-expose-ix-gille-polo-2009`), page 49.

For arbitrary group schemes `H` and `G` over `S`, the zero homomorphism has
underlying morphism `1`, meaning the unit of the group of morphisms over `S`.
The module proves that this condition characterizes zero, that arbitrary base
change preserves zero, and that zero is central on all test schemes. None of
these assertions requires `G` to be commutative.

`LocalCentralEquality H G` and `LocalTriviality H G` are predicates on the
fixed pair of group schemes. They express, respectively, clauses 5.1 and 5.2
without asserting them or attaching the source and base hypotheses of the
full theorem. They provide interfaces for composing local-rigidity inputs.

`local_triviality_of_local_central_equality` takes as a hypothesis the local
central-equality assertion for `H` and `G`, in precisely the form used by clause
5.1 of `MultiplicativeTypeCentralRigidityStatement`. It proves clause 5.2 for
the same groups by comparing the given homomorphism with zero. The fibre
hypothesis supplies equality with zero, whose centrality permits applying the
local assertion. The resulting equality with the base change of zero gives
triviality on the resulting open neighborhood.

This is a conditional reduction. It does not prove local central equality or
the complete published rigidity statement, and it does not assume any new
axioms or alter that statement.
