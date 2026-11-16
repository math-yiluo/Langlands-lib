# Rigidity of the numbered type-B Cartan matrix

This internal module transfers the published type-C rigidity argument to
Mathlib's actual type-B matrix. `IsTypeBNumbering M e` means that the
equivalence `e` identifies every ordered integral entry of `M` with
`CartanMatrix.B n`.

`CartanBNumbering.apply_eq_C` evaluates Mathlib's identity
`CartanMatrix.C_transpose`: a type-B entry at `(i,j)` is the type-C entry at
`(j,i)`. If `2 ≤ n`, every map preserving all type-B entries therefore
preserves all type-C entries, after reversing the two arguments. The
published `CartanCNumbering.rigid` fixes every vertex of that map.
`CartanBNumbering.unique` applies this result to the composite of one
numbering with the inverse of another, proving equality of the numberings.

The module is integral matrix combinatorics. It makes no existence or
classification assertion about group schemes. Its provenance is the
explicit transpose identity and composition of the published type-C
rigidity theorem, rather than a new translation from literature.
