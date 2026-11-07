# Tate's local functional equation

Worker 1248. This module proves the Fourier functional-equation clause of
`PadicAbelianLocalAnalysisStatement` (Tate's local functional equation, Tate's
thesis, local theory) for the published expressions, in the form
`fourier_functional_equation`: for every Schwartz–Bruhat `f` there is a
Schwartz–Bruhat `g` equal to the plus Fourier transform of `f`, and for any normal
meromorphic continuations `Z` of `ζ(f, χ, ·)` and `Y` of `ζ(g, χ⁻¹, ·)` the functions
`Y(1 - s) / L(χ⁻¹, 1 - s)` and `ε(χ, ψ, μ, s) Z(s) / L(χ, s)` agree on a punctured
neighbourhood of every point.

The implemented proof does not use Tate's Fubini argument.

1. `fe_strip_coset`: on the strip where `ζ(·, χ, s)` and `ζ(·, χ⁻¹, 1 - s)` both
   converge, the identity
   `ζ(f̂, χ⁻¹, 1 - s) L(χ⁻¹, 1 - s)⁻¹ = ε(s) ζ(f, χ, s) L(χ, s)⁻¹`
   holds for the indicator of a lattice coset `b + π^(-m) O`, whose Fourier transform
   is given by the Library lattice Fourier formula. If `b` lies in the lattice both
   sides are lattice zeta integrals (zero in the ramified case, the algebra
   `fe_algebra_lattice` in the unramified case). Otherwise both sides are
   `χ(b) |b|^(s-1) μ(π^(-m) O)` times, respectively, the lattice Gauss integral at level
   `n + j` (`j = -m - ord b ≥ 1`) and `ε(s)` restricted by `a ≤ j`; the ramified case is
   `setIntegral_additiveLattice_gauss_ramified` and the unramified case is
   `fe_algebra_shell`. The reciprocal Euler factors are explicit (`lFactorAt_inv_eq`).
2. `fe_strip`: the Library single-lattice expansion writes `f` as a finite combination
   of coset indicators; by `fourierTransform_eq_sum` and linearity of the zeta integral
   (integrability from Worker 1786's `zeta_integrable`) the identity holds for `f`.
3. `exists_convergesAt_strip`: the strip contains the real point
   `s = 1/2 + log |χ(π)| / log q`; it is open.
4. `fourier_functional_equation`: `g` is the Library Fourier closure of `f`. Both sides
   are meromorphic on `ℂ` and agree on the open strip, so Worker 1786's identity
   principle `meromorphic_germ_eq_of_eventuallyEq` gives equality of all punctured
   germs.
