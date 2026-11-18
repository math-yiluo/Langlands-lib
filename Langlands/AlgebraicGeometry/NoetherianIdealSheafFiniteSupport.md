# Finite support for sums of ideal sheaves

For an arbitrary Noetherian scheme and an arbitrary family of quasi-coherent
ideal sheaves represented by `Scheme.IdealSheafData`, `finiteSupSupport`
chooses a finite set of family indices whose sum is the full sum.
`finiteSupSupport_spec` states this equality; the supporting existence lemma
is `exists_finite_sup`.

This internal construction applies the Noetherian ascending-chain condition
locally. A finite affine cover exists by quasi-compactness. On each affine
chart its Noetherian coordinate ring makes the sum ideal compact in the
complete lattice of ideals, so finitely many family indices suffice there.
The union of these finite supports works on every chart. The existing local
criterion for inclusion of ideal sheaves proves the global equality.

This is supporting mathematics for finite detection of the full kernel in the
anti-affine quotient construction. It does not require the whole scheme to be
affine, and it asserts equality of ideal sheaves, including their nilpotent
structure. The provenance is derived from the published Mathlib Noetherian,
finite affine cover, compact ideal, and ideal-sheaf restriction APIs.
