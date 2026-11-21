# Archimedean slice comparisons for the actual cuspidal mixed functions

Let \(F\) be a number field with compact additive adele quotient. Take an
actual cuspidal operator realization of \(\mathrm{GL}_{r+1}\) over \(F\),
a supplied continuous unitary character acting as its central character,
and a supplied unitary form computing the canonical determinant-band
inner product. For a standard adelic additive character, suppose two
functionals on the resulting mixed smooth carrier satisfy the mixed
Whittaker covariance and derivative continuity at each compact open level.
The supplied algebraic map to the mixed space has the same underlying
values as the original Hilbert embedding. On each archimedean tensor slice
where the first restriction is nonzero, the two restrictions are
proportional. The statement assumes unitary archimedean Whittaker uniqueness.

Nonvanishing on the slice forces each fixed factor to be nonzero, by
multilinearity. The actual slice then has the compact open stabilizer and
the fixed-level Hilbert extension proved in `placeTensorFixedSmooth`.
The standard global additive character supplies the local unitary
character at the chosen place. The indexed comparison pulls both
functionals back to the same local smooth space, applies local uniqueness,
and restricts to each original value of the slice. This is an internal
step in the cuspidal multiplicity-one proof.
