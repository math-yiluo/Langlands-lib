# Galois cocycles of matrices over `L ⊗ D`

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisCocycle`.

Automorphisms `s` of a field `L` over `F` act on matrices over `L ⊗[F] D` entrywise
(`unitMap s.toAlgHom`). `IsCrossed c` is the proposition `c (s * t) = c s * s(c t)` for a map
`c : Gal(L/F) → GL_n(L ⊗ D)`, the cocycle identity of nonabelian Galois cohomology
(Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §1.1). `IsCrossed.map_one` gives `c 1 = 1`.

`IsCrossed.exists_coboundary` (Hilbert 90 for `GL_n(L ⊗ D)`, `F` infinite): every crossed
homomorphism is `c s = p * s(p)⁻¹` for a unit `p`. The proof identifies the entrywise action
with the semilinear action `coeffAut` of `Gal(L/F)` on the `L`-algebra
`L ⊗[F] M_n(D)` and applies `Langlands.Algebra.exists_unit_coboundary`.
