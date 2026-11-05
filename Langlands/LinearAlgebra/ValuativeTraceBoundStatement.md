# Valuative bounds detected by spanning trace probes

Author: Worker 1563.

`Langlands.ValuativeTraceBoundStatement.{u}` is an elementary auxiliary
target over an arbitrary field `F : Type u` with a valuative relation.
It concerns a set `S` of actual `Fin N` square matrices and a set `T` of
probe matrices whose `F`-linear span is the full matrix algebra.

For every probe `B` in `T`, the hypothesis gives a nonzero scalar bound
`b` for `trace(A * B)` as `A` ranges through `S`. The bound may depend on
`B`. The conclusion gives a single nonzero scalar bound for every entry
of every matrix in `S`. All comparisons use the given `≤ᵥ`.

The probe set need not be finite: the span condition already uses finite
linear combinations, and there are only finitely many matrix entries.
The statement includes `N = 0`, an empty set of tested matrices, and
trivial valuations. It assumes no topology, completeness, local
compactness, invertibility, or group structure.

This is internal derived linear algebra, obtained from linearity and
nondegeneracy of the actual matrix trace pairing and the elementary
valuative addition and multiplication laws. The intended proof extends
boundedness from the probes to their linear span, evaluates at the
standard single-entry matrices, and combines the finitely many
coordinate bounds. This file introduces a proposition target only.

The statement isolates the trace-duality step of a spectral boundedness
argument. It neither proves that a representation spans the matrix
algebra nor supplies group-theoretic density, semisimplicity, an
eigenvalue bound, or anisotropic compactness.
