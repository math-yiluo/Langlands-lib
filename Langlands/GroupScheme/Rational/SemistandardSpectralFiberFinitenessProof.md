# Finite and nonempty fibers over actual semistandard Levis

Worker 363, Task 7515. `Langlands.GroupScheme.semistandardSpectralFiberFiniteness`
proves `Langlands.GroupScheme.SemistandardSpectralFiberFinitenessStatement.{u}`.
The fiber models the set `P(M)` defined in Waldspurger (2003), I.1, printed
p. 238, whose cardinality occurs in the synthesis normalization in VI.3,
printed p. 305. These passages of the registered original
`waldspurger-2003-plancherel` were read directly.
[Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)

The proof applies the published
`semistandardSpectralFiberFiniteness_of_finiteness` to
`semistandardSpectralFiniteness`. The implication uses finiteness of a subtype
of the whole index and `nonempty_semistandardSpectralParabolicFiber`, which
extracts an index from the witness that the given Levi lies in the image.
The result concerns the full fiber over equality of the actual Levi subgroup
functors on every test scheme. It applies to the same arbitrary fields and
universe as the full-index theorem.
