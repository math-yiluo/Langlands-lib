# Proof of the lower bound by rank for the supercuspidal conductor

## Result

`supercuspidalConductorRankLowerBound : SupercuspidalConductorRankLowerBoundStatement.{uK, uV}`.
For every prime `p`, every `K : PadicField.{uK} p`, every `k : ℕ` and every irreducible
supercuspidal class `π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K (k + 1).succPNat`,

`((k + 2 : ℕ) : WithTop ℕ) ≤ Henniart.Numerical.conductor K π`.

The theorem has no hypotheses beyond those of the statement, and it covers depth zero.

## Proof

The theorem composes three results of the Library:

1. `finiteMatrixGaussInjectivity` (module
   `Langlands.BushnellKutzko.FiniteMatrixGaussInjectivityProof`): the finite matrix Gauss
   operator `v ↦ ∑_g ψ(tr g) ρ(g) v` of `GL_n` of a finite field is injective for every
   nontrivial additive character and every complex representation.
2. `standardDepthZeroShellNonzero_of_finiteMatrixGaussInjectivity` (module
   `Langlands.BushnellKutzko.DepthZeroShell`): Gauss injectivity gives
   `StandardDepthZeroShellNonzero`. For a nonzero vector fixed by the first unit group of the
   standard lattice chain, a smooth functional makes the integral over the shell
   `ord(det g) = -N` of the reflected zeta integrand of the indicator of `1 + ϖ M_N(𝔬_K)` nonzero.
   The integral reduces to the finite Gauss operator of the residue representation.
3. `supercuspidalConductorRankLowerBound_of_nonzeroShell` (module
   `Langlands.BushnellKutzko.SupercuspidalConductorDepthZeroReduction`):
   `StandardDepthZeroShellNonzero` implies the statement. At positive normalized level the
   higher-rank Swan formula gives `(a − N)₊ = N x > 0`. At normalized level zero, a nonzero
   vector fixed by the first unit group of the standard chain gives a nonzero extreme shell.
   The shell identity from the monomial functional equation then forces the Godement–Jacquet
   exponent to equal `N`, which is the first fixed level.

The universe parameters are passed through unchanged: the field lives in `Type uK` and the
representation spaces in `Type uV` throughout. The residue field of `K` is a finite field in
`Type uK`, and the space of vectors fixed by the kernel of reduction is a subspace of a
representation space in `Type uV`.

## Sources

Bushnell (1987), *Hereditary orders, Gauss sums and supercuspidal representations of GL_N*,
Theorem 3 and (5.1)(ii), (iv), printed pp. 198–199 and 208; Bushnell–Fröhlich (1985),
*Non-abelian congruence Gauss sums and p-adic simple algebras*, (3.3.8)(iv) and (3.3.10)–(3.3.15),
printed pp. 258–260. The Lean proof follows the depth-zero shell calculation. It proves the
needed Gauss injectivity by the elementary rank induction, without Kondo's formula.
