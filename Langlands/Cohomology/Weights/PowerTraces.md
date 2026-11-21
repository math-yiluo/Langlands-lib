# Complex realizations of power traces

Worker 951, Task 7903. The declarations are in `Langlands.Cohomology.Weights`.

`complexPowerTrace j A k` maps the trace of `A^k` to `ℂ` by the
field embedding `j : K →+* ℂ`. It does not require `j` to be continuous.
`complexPowerTrace_eq_rootPowerSum` says that if `A` is an invertible
endomorphism of a finite-dimensional `K`-space, the result equals
`rootPowerSum (A.charpoly.map j) k` for every natural `k`. There is no
semisimplicity hypothesis. `charpoly_eval_zero_ne_zero_of_isUnit` gives
nonvanishing of the constant term over the original coefficient field.

The proof uses a basis over `K`, then applies `j` to the matrix entries;
mapping commutes with powers, trace and characteristic polynomial. The
complex matrix is a unit. Apply the Library's cyclic triangularization
`Langlands.LieKolchin.exists_triangularizing_cyclic` to its `ℤ`-action.
Trace and characteristic polynomial are invariant under the resulting
conjugation. In the triangular basis, the `i`th diagonal entry of the
`k`th power is the `k`th power of the original diagonal entry. Indeed,
only the diagonal summand survives in the matrix product for that
entry. The determinant of the triangular characteristic matrix gives a
multiset of roots indexed by the same diagonal, counting repetitions.
For the nonvanishing lemma, evaluate `det(X I − A)` at zero and use
that determinant sends a matrix unit to a unit.

## Provenance and scope

This is the trace-to-power-sum step implicit in Kottwitz's passage from
(5.5) to (5.6), *On the λ-adic representations associated to some simple
Shimura varieties*, Invent. Math. 108 (1992), §5, printed p. 663. Source
`kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
It is an algebraic lemma on supplied operators, not a trace computation
on the Harris tower and not a construction of the local parameter.
