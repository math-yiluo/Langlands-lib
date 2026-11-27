# The special unitary Hasse principle at the Galois level

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisHasse`.

`suHasse σ hdim hsym n : SUHasse σ hdim hsym n` for every `n ≥ 1`: over a number field `F`,
for a central quaternion division algebra `D` with its canonical conjugation `τ` and every
invertible `τ`-antihermitian Gram matrix `H` over `D`, a special unitary crossed homomorphism
`Gal(L/F) → SU(H)(L ⊗ D)` with coboundary data at every completion is a coboundary of an
element of `SU(H)(L ⊗ D)`.

The proof combines `suHasse_of_rankOne` (induction on the rank via diagonalization and
`suHasse_adjoin`), `properWittAt` (proper Witt transitivity over every field of
characteristic zero) and `suHasse_one` (the Hasse norm theorem for the rank-one torus). This is
the injectivity of `H¹(K, SU) → ∏_v H¹(K_v, SU)` for skew-hermitian forms over a quaternion
division algebra over a number field, Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §5.11, printed p. 101, proved as in the case of
quadratic forms.
