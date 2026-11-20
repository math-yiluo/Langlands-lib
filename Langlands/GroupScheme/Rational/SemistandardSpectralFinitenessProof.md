# Finiteness of the intrinsic semistandard index

Worker 363, Task 7515. `Langlands.GroupScheme.semistandardSpectralFiniteness`
proves `Langlands.GroupScheme.SemistandardSpectralFinitenessStatement.{u}`.
Waldspurger defines semistandard parabolics with respect to a fixed maximal
split torus in I.1, printed pp. 238–239, and uses their Levi fibers in the
synthesis formula in VI.3, printed p. 305. These passages of the registered
original `waldspurger-2003-plancherel` were read directly. The Lean result is
an internal geometric deduction for the Library's arbitrary-field
group-scheme formulation. [Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)

`semistandardSpectralDynamicCoverage` from Task 7514 gives, for each intrinsic
triple, a cocharacter of the specified maximal split torus whose dynamic
triple is the given index. The proof chooses one such cocharacter per index.
It maps the index to a function from the subtype `relativeRoots i` to
`Ordering` by comparing each integer root pairing with zero.
`IsSplitTorus.finite_relativeRoots` applies because maximal splitness gives
splitness, connected reductivity gives affineness, and smoothness gives
local finite type. The function type is therefore finite.

If two functions agree, `compare_ge_iff_ge`, `compare_eq_iff_eq`, and
`compare_gt_iff_gt` give agreement of nonnegative, zero, and positive
pairings at every relative root. `relativeRootSignsDetermineDynamic`
then identifies the two dynamic parabolics, centralizers, and unipotent
radicals as subgroup functors on every test scheme.
`SemistandardSpectralIndex.ofCocharacter_eq` and the two realization
equalities identify the original indices. `Finite.of_injective` transfers
finiteness to the full index for every field in universe `u`.
