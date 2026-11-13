# Rigidity of the numbered Cartan matrix of type C

Author: Worker 244 for Task 6244.

This internal, derived module uses Mathlib's actual `CartanMatrix.C n`.
`IsTypeCNumbering M e` says that the equivalence `e` identifies every entry of
`M` with that matrix. For `2 ≤ n`, `CartanCNumbering.unique` proves that two
such numberings of the same matrix agree.

The proof first shows that an entry equals `2` precisely on the diagonal,
so every map preserving Cartan entries is injective. The unique entry equal
to `-2` fixes the final vertex. Strong induction on the distance from that
vertex fixes each earlier vertex: its image must be adjacent to the already
fixed next vertex; the alternative neighbor is either outside the path or
already fixed, contradicting injectivity.

This removes a numbering ambiguity in the intended distinguished-vertex
proof for division-algebra symplectic groups. The module is purely integral
combinatorics and makes no assertion about group schemes, root restrictions,
or the existence of any Tits index.
