# The descended Gram matrix of a special unitary Galois cocycle

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisGram`.

Let `L/F` be finite Galois and `c` a crossed homomorphism with values in `suGroup τ H L`.

- `gramOver_injective`, `exists_gramOver_eq_of_fixed`: matrices over `D` embed in matrices
  over `L ⊗ D`, and a Galois-fixed matrix over `L ⊗ D` comes from a matrix over `D`.
- `GramDescent τ H c` records a Hilbert 90 primitive `p` with `c s = p * s(p)⁻¹`
  (`coboundary`) and a matrix `gram = H'` over `D` with `p (1 ⊗ H') p* = 1 ⊗ H`
  (`gram_eq`).
- `exists_gramDescent` (`F` infinite): such data exist. The matrix `p⁻¹ (1 ⊗ H) (p⁻¹)*` is
  fixed by `Gal(L/F)` because every `c s` preserves `1 ⊗ H`, so it descends to `D`.

This is the twisting argument identifying `H¹(L/F, U(h))` with isometry classes of forms that
become isometric to `h` over `L` (twisting, Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §1.4).
