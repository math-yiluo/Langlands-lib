# Finiteness of central unipotent rational points

Author: Worker 1532.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Internal helper for the
proof of `CentralNormKernelCompactnessStatement`.

`finite_centralUnipotent`: let `K` be algebraically closed, `G` a group scheme over `Spec K` with
`G.X.left` affine and `G.X.hom` locally of finite type, `hG : HasTrivialUnipotentRadical G`,
`z : Z ⟶ G` with `IsSchemeTheoreticCenter z`, and `ρ : MatrixRepresentation G N` a closed
immersion. Then the set of central rational points `g` with `ρ.rationalMatrix g - 1` nilpotent
is finite.

Proof.

1. Choose spectral data `D` for `CentralAlgebra ρ` (module `Decomposition`, which applies since
   the algebra is finite-dimensional over `K`). Let `Φ : G ⟶ 𝔾_m^r` be the product
   (`Pi.lift`) of the block characters `blockChar D i` (module `CentralAlgebra`), with target the
   split torus on `ULift (Fin r)`, which is affine (`isAffineHom_splitTorus`).
2. Let `S` be the kernel of `z ≫ Φ` (`GroupScheme.kernel`, a closed immersion into `Z` because
   the target is separated) and `s = kernelι ≫ z : S ⟶ G`. Then `s` is a closed subgroup, and it
   is central because `z` represents the centre.
3. For a rational point `y` of `S`, the point `g = y ≫ s` is central with all block characters
   trivial: `det (ρ(g) E i + (1 - E i)) = 1`. By `SpectralData.det_block` this determinant is
   `χ i (ρ g) ^ a` with `1 ≤ a ≤ N`, so `χ i (ρ g) ^ (N!) = 1`. Every eigenvalue of `ρ(g)` is one
   of the `χ i (ρ g)` (`SpectralData.exists_eq_of_isRoot`). So
   `finite_rationalPoints_of_eigenvalues` (module `CentralFiniteness`) applies with `m = N!`:
   `S` has finitely many rational points.
4. A central `g` with `ρ(g) - 1` nilpotent has `χ i (ρ g) = 1` for all `i`
   (`χ_eq_one_of_isNilpotent`), so all its block determinants are `1` and `g ≫ Φ = 1`
   (components of a product point, `piPointsEquiv`). Writing `g = w ≫ z` (range of `z` is the
   centre), `w` lies in the kernel, so `g` is the image of a rational point of `S`
   (`kernelPointsEquiv`). The set in question is therefore contained in the finite range of
   `y ↦ y ≫ s`.
