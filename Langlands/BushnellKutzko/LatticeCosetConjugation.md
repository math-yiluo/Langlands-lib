# Formal intertwining and conjugation of a lattice coset

`latticeCosetIntertwining b D` is the set of units whose conjugate of the
coset `b + D` meets that coset. When `D` is the error step of a stratum,
this recovers `Stratum.formalSelfIntertwining`.

`exists_conj_sub_mem_filtration_of_adjoint_image` performs the finite
correction used in BK93 (3.3.12)–(3.3.13). Suppose the error submodule
`D` is the sum of the adjoint image of a positive-depth submodule `J`
and a filtration step `P^t`. Suppose that multiplication by `J` on
either side preserves `D`, and a subgroup consists of the units with
difference from one in `J`. For an error in `D` at depth `k < t`, choose
an adjoint correction so that its linear term cancels the error modulo
`P^t`. Conjugation by one plus that correction leaves a new error in
`D` at depth at least `k + 1`. Every remaining product contains an
extra factor from `J`, including the term from the inverse unit.
Induction on the number of steps to `t` supplies a single conjugating
unit in the subgroup.

`latticeCoset_conj_sub_mem_of_adjoint_image` gives the invariance of the
larger coset from the same multiplication bounds and adjoint-image
inclusion. `latticeCosetIntertwining_eq_sandwich` then gives the formal
intertwining set of the larger coset from the smaller one. For a unit
intertwining the larger coset, correct both representatives into the
smaller coset to get a unit intertwining that coset. The corrections
supply the two outer factors. Invariance of the larger coset gives the
reverse inclusion.

The source is Bushnell–Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), source ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`,
(3.3.6)–(3.3.7), printed p. 107 (PDF p. 119), and (3.3.10)–(3.3.13),
printed pp. 109–110 (PDF pp. 121–122).
