# Double-coset covers for the finite block parabolic

Finite adelic Iwasawa writes each finite adelic matrix as an upper triangular
matrix times an element of the standard integral subgroup. The upper triangular
factor belongs to the standard block parabolic. The image of the compact
integral subgroup therefore covers the quotient on the left by that parabolic.

For every open subgroup acting on the right, apply the Library's finite
double-coset cover of a compact left quotient.
`finiteBlockParabolicDoubleCosetReps` chooses a finite set whose double
cosets cover the finite adelic group, as certified by
`finiteBlockParabolicDoubleCosetReps_cover`. This is an internal consequence
of the Library's finite Iwasawa and compact quotient results for sampling
the cuspidal slices of a global constant term.
